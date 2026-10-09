// This file is part of Crag.
//
// Copyright (C) 2026 Ralf Claussnitzer
//
// Crag is free software: you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version.
//
// Crag is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with
// Crag. If not, see <https://www.gnu.org/licenses/>.

//! The allocator, after mimalloc (Plan §11.4.11).
//!
//! Memory comes in segments of [`SEGMENT_SIZE`] bytes, aligned to their
//! size, so the segment of a block is its address with the low bits
//! cleared. A segment is split into pages of [`PAGE_SIZE`] bytes, and its
//! first bytes describe them. A page in use holds blocks of one size class.
//!
//! Each worker has its own [`Heap`], and each page belongs to one heap. A
//! page keeps two free lists: its own, which only the owning heap touches,
//! and the thread-free list, onto which other threads push the blocks they
//! free. The owner moves the thread-free list over to its own when it runs
//! out, so neither allocating nor freeing takes a lock.
//!
//! Generated code allocates inline from the free list of the class's
//! current page (see `crag_abi`) and calls `rt_alloc` only when it is
//! empty, or for a block above [`SMALL_SIZE_MAX`], which gets a segment of
//! its own.
//!
//! A heap that is dropped unmaps the segments without live blocks. It
//! leaves the others mapped, so blocks other threads still hold stay valid,
//! and their frees go to thread-free lists that nobody collects: those
//! segments are abandoned until a later heap adopts them, which comes with
//! the scheduler (Plan §11.7.1).

use std::mem::offset_of;
use std::ptr::null_mut;
use std::sync::atomic::{AtomicPtr, AtomicU64, Ordering};

use crag_abi::{
    COUNT_OFFSET, PAGE_FREE_OFFSET, PAGE_USED_OFFSET, SIZE_CLASSES, SMALL_SIZE_MAX,
    TYPE_INDEX_OFFSET, class_size, size_class,
};

use crate::die;
use crate::fiber::TaskContext;

/// Bytes of a segment, which is also its alignment.
pub const SEGMENT_SIZE: usize = 4 << 20;

/// Bytes of a page. The first page of a segment is smaller by the
/// segment's header.
pub const PAGE_SIZE: usize = 64 << 10;

const PAGES: usize = SEGMENT_SIZE / PAGE_SIZE;

/// Bytes of a page's unused end that a refill turns into free blocks at a
/// time, so a fresh page is not touched all at once.
const EXTEND_BYTES: usize = 4096;

/// What the operating system maps in.
const OS_PAGE: usize = 4096;

/// A free block: its first word links the next.
#[repr(C)]
struct Block {
    next: *mut Block,
}

/// A page's descriptor, in its segment's header.
#[repr(C)]
pub(crate) struct Page {
    /// The owner's free list; generated code pops from it.
    free: *mut Block,
    /// Blocks handed out and not yet back on `free`, those on the
    /// thread-free list included.
    used: usize,
    /// Blocks other threads freed.
    thread_free: AtomicPtr<Block>,
    /// The id of the owning heap; zero while the page is not in use. It
    /// never names another heap while blocks of the page are live, so a
    /// stale read on another thread still sees an id that is not its own.
    owner: AtomicU64,
    /// Bytes of a block; zero while the page is not in use.
    block_size: usize,
    class: usize,
    /// The part of the page not yet carved into blocks.
    bump: usize,
    end: usize,
}

const _: () = assert!(offset_of!(Page, free) == PAGE_FREE_OFFSET as usize);
const _: () = assert!(offset_of!(Page, used) == PAGE_USED_OFFSET as usize);

impl Page {
    const fn unused() -> Page {
        Page {
            free: null_mut(),
            used: 0,
            thread_free: AtomicPtr::new(null_mut()),
            owner: AtomicU64::new(0),
            block_size: 0,
            class: 0,
            bump: 0,
            end: 0,
        }
    }
}

/// The page of every class that has none: its free list is always empty,
/// so the inline path falls through to `rt_alloc`. Nothing writes to it.
struct EmptyPage(Page);

// SAFETY: the page is never written; its pointers are null.
unsafe impl Sync for EmptyPage {}

static EMPTY: EmptyPage = EmptyPage(Page::unused());

fn empty_page() -> *mut Page {
    (&raw const EMPTY.0).cast_mut()
}

/// A segment's header.
#[repr(C)]
struct Segment {
    pages: [Page; PAGES],
    /// Mapped bytes if the segment holds one large block, else zero.
    huge: usize,
    /// Pages in use.
    used_pages: usize,
}

/// Where the first page's blocks begin.
const SEGMENT_HEADER: usize = size_of::<Segment>().next_multiple_of(64);

const _: () = assert!(SEGMENT_HEADER < PAGE_SIZE / 2);
const _: () = assert!(SMALL_SIZE_MAX as usize <= PAGE_SIZE / 4);

fn segment_of(ptr: usize) -> *mut Segment {
    (ptr & !(SEGMENT_SIZE - 1)) as *mut Segment
}

/// The bytes of a page's blocks: after the header for the first page.
fn page_area(page: *const Page) -> (usize, usize) {
    let segment = page as usize & !(SEGMENT_SIZE - 1);
    let index = (page as usize - segment) / size_of::<Page>();
    let start = match index {
        0 => segment + SEGMENT_HEADER,
        _ => segment + index * PAGE_SIZE,
    };
    (start, segment + (index + 1) * PAGE_SIZE)
}

/// Maps `size` bytes, a multiple of the OS page, at an address aligned to
/// `SEGMENT_SIZE`. The memory reads as zero.
fn map_segment(size: usize) -> *mut Segment {
    let over = size + SEGMENT_SIZE;
    // SAFETY: a fresh anonymous mapping that aliases nothing; the parts
    // unmapped again lie inside it.
    unsafe {
        let base = libc::mmap(
            null_mut(),
            over,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
            -1,
            0,
        );
        if base == libc::MAP_FAILED {
            die("out of memory");
        }
        let base = base as usize;
        let start = base.next_multiple_of(SEGMENT_SIZE);
        if start > base {
            libc::munmap(base as *mut libc::c_void, start - base);
        }
        let tail = base + over - (start + size);
        if tail > 0 {
            libc::munmap((start + size) as *mut libc::c_void, tail);
        }
        start as *mut Segment
    }
}

/// # Safety
///
/// `segment` came from `map_segment` with this size, and nothing uses it
/// any more.
unsafe fn unmap_segment(segment: *mut Segment, size: usize) {
    // SAFETY: as the caller promises.
    unsafe { libc::munmap(segment as *mut libc::c_void, size) };
}

static NEXT_HEAP_ID: AtomicU64 = AtomicU64::new(1);

/// A worker's heap. Generated code finds it through the task context and
/// reads `pages` by offset.
#[repr(C)]
pub struct Heap {
    /// For each size class, the page allocated from.
    pages: [*mut Page; SIZE_CLASSES],
    id: u64,
    /// For each size class, its pages in use, the current one among them.
    classes: [Vec<*mut Page>; SIZE_CLASSES],
    segments: Vec<*mut Segment>,
    /// Pages of this heap's segments not in use.
    free_pages: Vec<*mut Page>,
}

const _: () = assert!(offset_of!(Heap, pages) == 0);

// SAFETY: a heap is used by one thread at a time, through `&mut`. What it
// shares with other threads, the thread-free lists, is atomic.
unsafe impl Send for Heap {}

impl Default for Heap {
    fn default() -> Heap {
        Heap::new()
    }
}

impl Heap {
    pub fn new() -> Heap {
        Heap {
            pages: [empty_page(); SIZE_CLASSES],
            id: NEXT_HEAP_ID.fetch_add(1, Ordering::Relaxed),
            classes: std::array::from_fn(|_| Vec::new()),
            segments: Vec::new(),
            free_pages: Vec::new(),
        }
    }

    /// A block of at least `size` bytes, aligned to eight. Its contents
    /// are undefined.
    pub fn alloc(&mut self, size: usize) -> *mut u8 {
        let Some(class) = u32::try_from(size).ok().and_then(size_class) else {
            return self.alloc_huge(size);
        };
        let page = self.pages[class as usize];
        // SAFETY: the current page is the empty page or a page in use of
        // this heap; the empty page's free list is null.
        unsafe {
            let block = (*page).free;
            if block.is_null() {
                return self.alloc_slow(class as usize);
            }
            (*page).free = (*block).next;
            (*page).used += 1;
            block.cast()
        }
    }

    /// The path of `alloc` when the current page has no free block: refill
    /// it from its thread-free list or its unused end, or move on to
    /// another page of the class, a fresh one if none has room.
    pub fn alloc_slow(&mut self, class: usize) -> *mut u8 {
        let current = self.pages[class];
        let page = match current != empty_page() && refill(current) {
            true => current,
            false => {
                let other = self.classes[class]
                    .iter()
                    .copied()
                    .find(|&p| p != current && refill(p));
                let page = other.unwrap_or_else(|| self.new_page(class));
                self.pages[class] = page;
                page
            }
        };
        // SAFETY: the page is in use by this heap and has a free block.
        unsafe {
            let block = (*page).free;
            (*page).free = (*block).next;
            (*page).used += 1;
            block.cast()
        }
    }

    /// A segment holding the one block.
    fn alloc_huge(&mut self, size: usize) -> *mut u8 {
        let Some(mapped) = size
            .checked_add(SEGMENT_HEADER + OS_PAGE)
            .map(|s| s & !(OS_PAGE - 1))
        else {
            die("out of memory");
        };
        let segment = map_segment(mapped);
        // SAFETY: the mapping is fresh and starts with the header.
        unsafe { (*segment).huge = mapped };
        (segment as usize + SEGMENT_HEADER) as *mut u8
    }

    fn new_page(&mut self, class: usize) -> *mut Page {
        if self.free_pages.is_empty() {
            self.new_segment();
        }
        let page = self.free_pages.pop().expect("a fresh segment has pages");
        let size = class_size(class as u32) as usize;
        let (start, end) = page_area(page);
        // SAFETY: the page is not in use, so this heap alone refers to it.
        unsafe {
            (*page).free = null_mut();
            (*page).used = 0;
            (*page).block_size = size;
            (*page).class = class;
            (*page).bump = start;
            (*page).end = start + (end - start) / size * size;
            (*page).owner.store(self.id, Ordering::Relaxed);
            (*segment_of(page as usize)).used_pages += 1;
            refill(page);
        }
        self.classes[class].push(page);
        page
    }

    fn new_segment(&mut self) {
        let segment = map_segment(SEGMENT_SIZE);
        self.segments.push(segment);
        // The mapping reads as zero, which is an unused page and a segment
        // of pages with none in use. Hand out the first page last.
        // SAFETY: the pages lie in the fresh header.
        let pages = unsafe { &raw mut (*segment).pages };
        for i in (0..PAGES).rev() {
            // SAFETY: as above.
            self.free_pages
                .push(unsafe { (&raw mut (*pages)[i]).cast() });
        }
    }

    /// Gives a block back.
    ///
    /// # Safety
    ///
    /// `ptr` came from `alloc` of some heap, possibly on another thread, and
    /// is not used again. That heap's segment must still be mapped, which
    /// holds while the block is live.
    pub unsafe fn free(&mut self, ptr: *mut u8) {
        let segment = segment_of(ptr as usize);
        // SAFETY: the block lies in a live segment, whose header describes
        // its page; only this heap touches the page's own free list if it
        // owns it.
        unsafe {
            if (*segment).huge != 0 {
                unmap_segment(segment, (*segment).huge);
                return;
            }
            let index = (ptr as usize - segment as usize) / PAGE_SIZE;
            let page: *mut Page = (&raw mut (*segment).pages[index]).cast();
            let block = ptr.cast::<Block>();
            if (*page).owner.load(Ordering::Relaxed) == self.id {
                (*block).next = (*page).free;
                (*page).free = block;
                (*page).used -= 1;
                if (*page).used == 0 && self.pages[(*page).class] != page {
                    self.retire(page);
                }
            } else {
                let mut head = (*page).thread_free.load(Ordering::Relaxed);
                loop {
                    (*block).next = head;
                    match (*page).thread_free.compare_exchange_weak(
                        head,
                        block,
                        Ordering::Release,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => break,
                        Err(now) => head = now,
                    }
                }
            }
        }
    }

    /// Takes a page without blocks in use out of its class. A segment
    /// whose pages are all unused is unmapped, unless it is the last.
    ///
    /// # Safety
    ///
    /// The page is in use by this heap, not current, and has no block in
    /// use.
    unsafe fn retire(&mut self, page: *mut Page) {
        // SAFETY: as the caller promises.
        unsafe {
            let class = (*page).class;
            let list = &mut self.classes[class];
            let at = list.iter().position(|&p| p == page).expect("in its class");
            list.swap_remove(at);
            *page = Page::unused();
            let segment = segment_of(page as usize);
            (*segment).used_pages -= 1;
            if (*segment).used_pages == 0 && self.segments.len() > 1 {
                let base = segment as usize;
                self.free_pages
                    .retain(|&p| !(base..base + SEGMENT_SIZE).contains(&(p as usize)));
                self.segments.retain(|&s| s != segment);
                unmap_segment(segment, SEGMENT_SIZE);
            } else {
                self.free_pages.push(page);
            }
        }
    }

    /// Segments this heap has mapped, not counting large blocks.
    pub fn segments(&self) -> usize {
        self.segments.len()
    }

    /// Pages in use, over all classes.
    pub fn pages_in_use(&self) -> usize {
        self.classes.iter().map(Vec::len).sum()
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        for &segment in &self.segments {
            let mut live = false;
            for i in 0..PAGES {
                // SAFETY: the segment is mapped and this heap's.
                let page: *mut Page = unsafe { (&raw mut (*segment).pages[i]).cast() };
                // SAFETY: as above.
                if unsafe { (*page).block_size } != 0 {
                    collect(page);
                    // SAFETY: as above.
                    live |= unsafe { (*page).used } != 0;
                }
            }
            if !live {
                // SAFETY: no block of the segment is live, so nothing can
                // refer to it, not even another thread's free.
                unsafe { unmap_segment(segment, SEGMENT_SIZE) };
            }
        }
    }
}

/// Moves the thread-free list of a page in use over to its own.
fn collect(page: *mut Page) {
    // SAFETY: called by the owner of a page in use. The swap takes the list
    // whole; acquiring it makes the links the other threads wrote visible.
    unsafe {
        let mut block = (*page).thread_free.swap(null_mut(), Ordering::Acquire);
        while !block.is_null() {
            let next = (*block).next;
            (*block).next = (*page).free;
            (*page).free = block;
            (*page).used -= 1;
            block = next;
        }
    }
}

/// Gives a page in use free blocks if it can: those other threads freed,
/// else some of its unused end. Whether it has a free block now.
fn refill(page: *mut Page) -> bool {
    collect(page);
    // SAFETY: called by the owner of a page in use.
    unsafe {
        if (*page).free.is_null() && (*page).bump < (*page).end {
            let size = (*page).block_size;
            let stop = (*page).end.min((*page).bump + EXTEND_BYTES.max(size));
            let mut at = stop - (stop - (*page).bump) % size;
            while at > (*page).bump {
                at -= size;
                let block = at as *mut Block;
                (*block).next = (*page).free;
                (*page).free = block;
            }
            (*page).bump = stop - (stop - (*page).bump) % size;
        }
        !(*page).free.is_null()
    }
}

/// A box of `size` bytes from `heap`, with a count of one and `type_index`
/// in its header (Compiler Architecture §11.1). Its fields are undefined.
pub fn alloc_box(heap: &mut Heap, size: usize, type_index: u64) -> *mut u8 {
    let ptr = heap.alloc(size);
    // SAFETY: a box is at least its header, which the block holds.
    unsafe {
        ptr.offset(COUNT_OFFSET as isize).cast::<u64>().write(1);
        ptr.offset(TYPE_INDEX_OFFSET as isize)
            .cast::<u64>()
            .write(type_index);
    }
    ptr
}

/// `rt_alloc(ctx, size, type_index)`: see `crag_abi::RuntimeFn::Alloc`.
///
/// Called with the C convention when the inline path finds no free block.
/// It switches to the system stack, keeping the fiber's stack pointer in a
/// callee-saved register, and allocates there.
///
/// # Safety
///
/// Only generated code may call this, on a fiber stack, with the fiber's
/// task context.
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn rt_alloc(
    ctx: *const TaskContext,
    size: u64,
    type_index: u64,
) -> *mut u8 {
    std::arch::naked_asm!(
        "push rbx",
        "mov rbx, rsp",
        "mov rax, [rdi + {worker}]",
        "mov rsp, [rax]",
        "and rsp, -16",
        "call {slow}",
        "mov rsp, rbx",
        "pop rbx",
        "ret",
        worker = const offset_of!(TaskContext, worker),
        slow = sym alloc_slow_entry,
    )
}

/// The Rust half of `rt_alloc`, on the system stack.
///
/// # Safety
///
/// Called only by `rt_alloc`, while a worker runs the fiber of `ctx`.
unsafe extern "C" fn alloc_slow_entry(
    ctx: *const TaskContext,
    size: u64,
    type_index: u64,
) -> *mut u8 {
    // SAFETY: `Worker::resume` stored its heap in the context, and nothing
    // else uses the heap while the fiber runs.
    unsafe {
        let heap = &mut *(*ctx).heap.load(Ordering::Relaxed);
        alloc_box(heap, size as usize, type_index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_are_distinct_and_reused_after_free() {
        let mut heap = Heap::new();
        let blocks: Vec<*mut u8> = (0..10_000).map(|_| heap.alloc(24)).collect();
        let mut sorted = blocks.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(sorted.len(), blocks.len());
        for w in sorted.windows(2) {
            assert!(w[1] as usize - w[0] as usize >= 24);
        }
        for &b in &blocks {
            assert!((b as usize).is_multiple_of(8));
            // SAFETY: the block holds 24 bytes.
            unsafe { b.write_bytes(0xab, 24) };
        }
        let pages = heap.pages_in_use();
        for &b in &blocks {
            // SAFETY: from this heap, freed once.
            unsafe { heap.free(b) };
        }
        // All pages but the current one are retired.
        assert_eq!(heap.pages_in_use(), 1);
        let again: Vec<*mut u8> = (0..10_000).map(|_| heap.alloc(24)).collect();
        assert_eq!(heap.pages_in_use(), pages);
        assert_eq!(heap.segments(), 1);
        for b in again {
            // SAFETY: as above.
            unsafe { heap.free(b) };
        }
    }

    #[test]
    fn every_class_and_large_blocks() {
        let mut heap = Heap::new();
        for size in [1, 8, 9, 64, 65, 200, 1000, 8192, 8193, 100_000, 5 << 20] {
            let blocks: Vec<*mut u8> = (0..50).map(|_| heap.alloc(size)).collect();
            for &b in &blocks {
                // SAFETY: each block holds `size` bytes.
                unsafe { b.write_bytes(size as u8, size) };
            }
            for &b in &blocks {
                // SAFETY: as above.
                unsafe {
                    assert_eq!(*b, size as u8);
                    assert_eq!(*b.add(size - 1), size as u8);
                    heap.free(b);
                }
            }
        }
    }

    #[test]
    fn segments_are_unmapped_when_empty() {
        let mut heap = Heap::new();
        // More than a segment's worth of 4 KiB blocks.
        let blocks: Vec<*mut u8> = (0..3000).map(|_| heap.alloc(4096)).collect();
        assert!(heap.segments() >= 2);
        for b in blocks {
            // SAFETY: from this heap, freed once.
            unsafe { heap.free(b) };
        }
        assert_eq!(heap.segments(), 1);
    }

    #[test]
    fn frees_from_other_threads_come_back() {
        let mut heap = Heap::new();
        let blocks: Vec<usize> = (0..20_000).map(|_| heap.alloc(48) as usize).collect();
        let pages = heap.pages_in_use();
        std::thread::scope(|s| {
            for chunk in blocks.chunks(5000) {
                s.spawn(move || {
                    let mut other = Heap::new();
                    for &b in chunk {
                        // SAFETY: each block is freed once, by one thread.
                        unsafe { other.free(b as *mut u8) };
                    }
                });
            }
        });
        // The blocks wait on thread-free lists until allocation collects
        // them, so allocating as many again needs no new page. Only the
        // current page's unused end adds blocks not seen before.
        let again: Vec<*mut u8> = (0..20_000).map(|_| heap.alloc(48)).collect();
        assert_eq!(heap.pages_in_use(), pages);
        let old: std::collections::HashSet<usize> = blocks.into_iter().collect();
        let reused = again
            .iter()
            .filter(|&&b| old.contains(&(b as usize)))
            .count();
        assert!(reused >= 20_000 - PAGE_SIZE / 48, "{reused}");
    }

    #[test]
    fn boxes_have_a_header() {
        let mut heap = Heap::new();
        let b = alloc_box(&mut heap, 32, 7).cast::<u64>();
        // SAFETY: a fresh box of four words.
        unsafe {
            assert_eq!(*b, 1);
            assert_eq!(*b.add(1), 7);
            heap.free(b.cast());
        }
    }
}
