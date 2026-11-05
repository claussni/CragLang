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

//! Usage counts (Implementation Plan §11.12.10): with `CRAG_AGENT_STATS=1`
//! the diagnostic codes hit through the agent server are counted, per code
//! and day, in `agent-stats` under the Crag home. `:agent-stats` in the
//! REPL shows the most frequent. Nothing leaves the machine.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

use crag_diag::DiagCode;

/// Where the counts go, when the user opted in.
fn opted_in() -> Option<PathBuf> {
    if std::env::var_os("CRAG_AGENT_STATS").is_none_or(|v| v != "1") {
        return None;
    }
    stats_file()
}

fn stats_file() -> Option<PathBuf> {
    Some(crag_package::home::crag_home()?.join("agent-stats"))
}

/// Counts the codes against today, when the user opted in.
pub(crate) fn count(codes: impl Iterator<Item = DiagCode>) {
    let codes: Vec<DiagCode> = codes.collect();
    if codes.is_empty() {
        return;
    }
    let Some(file) = opted_in() else {
        return;
    };
    let mut counts = read(&file);
    let today = today();
    for code in codes {
        *counts.entry((today.clone(), code.to_string())).or_default() += 1;
    }
    let mut out = String::new();
    for ((day, code), n) in &counts {
        let _ = writeln!(out, "{day} {code} {n}");
    }
    if let Some(dir) = file.parent() {
        let _ = std::fs::create_dir_all(dir);
    }
    let _ = std::fs::write(&file, out);
}

/// The counts on file: by day and code.
fn read(file: &PathBuf) -> BTreeMap<(String, String), u64> {
    let mut counts = BTreeMap::new();
    let Ok(text) = std::fs::read_to_string(file) else {
        return counts;
    };
    for line in text.lines() {
        let mut words = line.split_whitespace();
        if let (Some(day), Some(code), Some(n)) = (words.next(), words.next(), words.next())
            && let Ok(n) = n.parse::<u64>()
        {
            *counts
                .entry((day.to_string(), code.to_string()))
                .or_default() += n;
        }
    }
    counts
}

/// The most frequent codes over every counted day, for `:agent-stats`.
pub(crate) fn report() -> String {
    let counts = stats_file().map(|f| read(&f)).unwrap_or_default();
    if counts.is_empty() {
        return "no agent stats are counted; the user opts in with CRAG_AGENT_STATS=1\n".into();
    }
    let mut by_code: BTreeMap<String, u64> = BTreeMap::new();
    for ((_, code), n) in &counts {
        *by_code.entry(code.clone()).or_default() += n;
    }
    let mut rows: Vec<(String, u64)> = by_code.into_iter().collect();
    rows.sort_by_key(|(code, n)| (std::cmp::Reverse(*n), code.clone()));
    let mut out = String::new();
    for (code, n) in rows.iter().take(20) {
        let title = DiagCode::parse(code).map_or("", |c| c.entry().title);
        let _ = writeln!(out, "{n:>6}  {code}  {title}");
    }
    out
}

/// Today as `2026-11-05`, from the system clock.
fn today() -> String {
    let days = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_secs() / 86_400) as i64;
    // Civil-from-days, as in Howard Hinnant's date algorithms.
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let year = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let (month, year) = if mp < 10 {
        (mp + 3, year)
    } else {
        (mp - 9, year + 1)
    };
    format!("{year:04}-{month:02}-{day:02}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_clock_gives_a_civil_date() {
        // 2026-11-05 is day 20762 after the epoch.
        let date = today();
        assert_eq!(date.len(), 10, "{date}");
        assert!(date.starts_with("20"), "{date}");
    }
}
