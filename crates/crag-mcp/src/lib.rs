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

//! The facade over the Model Context Protocol SDK (Implementation Plan
//! §11.12.1): the agent server's tools are plain functions on JSON, and
//! only this crate knows `rmcp`, so the protocol version can move without
//! touching them, as `crag-db` does for Salsa and `crag-codegen` for
//! Cranelift.
//!
//! The SDK is asynchronous; the tools are not. A handler lives on a thread
//! of its own and takes one call at a time, in the order they came, while
//! the protocol runs on a single-threaded runtime beside it.

use std::io;
use std::sync::mpsc;

use rmcp::model::{
    CallToolRequestParams, CallToolResponse, CallToolResult, Implementation, ListToolsResult,
    PaginatedRequestParams, ServerCapabilities, ServerConfig, Tool, ToolAnnotations,
};
use rmcp::service::RequestContext;
use rmcp::{ErrorData, RoleServer, ServerHandler, ServiceExt};
use serde_json::{Map, Value};

/// A tool as the server advertises it.
#[derive(Clone, Debug)]
pub struct ToolSpec {
    pub name: &'static str,
    pub title: &'static str,
    pub description: &'static str,
    /// The JSON schema of its arguments: an object schema.
    pub input_schema: Value,
    /// Whether it changes files or images, so that clients confirm it.
    pub destructive: bool,
}

/// How a call went that reached its tool.
#[derive(Clone, Debug, PartialEq)]
pub enum Outcome {
    /// The tool's answer.
    Done(Value),
    /// The tool ran and failed, as its caller should see: the answer says
    /// why.
    Failed(Value),
}

/// A call that never reached a tool.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CallError {
    UnknownTool(String),
    InvalidArguments(String),
}

/// What answers the calls.
pub trait Handler {
    fn call(&mut self, tool: &str, args: &Map<String, Value>) -> Result<Outcome, CallError>;
}

/// The server's name and version, and what it tells a client about itself.
#[derive(Clone, Debug)]
pub struct Info {
    pub name: String,
    pub version: String,
    pub instructions: String,
}

/// A call on its way to the handler's thread, with where its answer goes.
struct Job {
    tool: String,
    args: Map<String, Value>,
    answer: tokio::sync::oneshot::Sender<Result<Outcome, CallError>>,
}

struct Facade {
    info: Info,
    tools: Vec<Tool>,
    jobs: mpsc::Sender<Job>,
}

/// The tool as the protocol describes it.
fn tool(spec: &ToolSpec) -> Tool {
    let schema = match &spec.input_schema {
        Value::Object(schema) => schema.clone(),
        _ => Map::new(),
    };
    Tool::new(spec.name, spec.description, schema)
        .with_title(spec.title)
        .with_annotations(
            ToolAnnotations::with_title(spec.title)
                .read_only(!spec.destructive)
                .destructive(spec.destructive),
        )
}

impl ServerHandler for Facade {
    fn get_info(&self) -> ServerConfig {
        ServerConfig::new(ServerCapabilities::builder().enable_tools().build())
            .with_server_info(Implementation::new(&self.info.name, &self.info.version))
            .with_instructions(&self.info.instructions)
    }

    async fn list_tools(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> Result<ListToolsResult, ErrorData> {
        Ok(ListToolsResult::with_all_items(self.tools.clone()))
    }

    fn get_tool(&self, name: &str) -> Option<Tool> {
        self.tools.iter().find(|t| t.name == name).cloned()
    }

    async fn call_tool(
        &self,
        request: CallToolRequestParams,
        _context: RequestContext<RoleServer>,
    ) -> Result<CallToolResponse, ErrorData> {
        let (answer, answered) = tokio::sync::oneshot::channel();
        let job = Job {
            tool: request.name.to_string(),
            args: request.arguments.unwrap_or_default(),
            answer,
        };
        let stopped = || ErrorData::internal_error("the agent server stopped", None);
        self.jobs.send(job).map_err(|_| stopped())?;
        match answered.await.map_err(|_| stopped())? {
            Ok(Outcome::Done(value)) => Ok(CallToolResult::structured(value).into()),
            Ok(Outcome::Failed(value)) => Ok(CallToolResult::structured_error(value).into()),
            Err(CallError::UnknownTool(name)) => Err(ErrorData::invalid_params(
                format!("there is no tool `{name}`"),
                None,
            )),
            Err(CallError::InvalidArguments(why)) => Err(ErrorData::invalid_params(why, None)),
        }
    }
}

/// Serves the tools over standard input and `output` until the input ends.
/// `make` builds the handler on its own thread, so it need not be `Send`.
pub fn serve<H, F>(info: Info, tools: &[ToolSpec], make: F, output: std::fs::File) -> io::Result<()>
where
    H: Handler,
    F: FnOnce() -> H + Send + 'static,
{
    let (jobs, queue) = mpsc::channel::<Job>();
    let worker = std::thread::Builder::new()
        .name("agent-tools".into())
        .spawn(move || {
            let mut handler = make();
            for job in queue {
                let answer = handler.call(&job.tool, &job.args);
                // A client that went away no longer waits for it.
                let _ = job.answer.send(answer);
            }
        })?;
    let facade = Facade {
        info,
        tools: tools.iter().map(tool).collect(),
        jobs,
    };
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    let served = runtime.block_on(async move {
        let output = tokio::fs::File::from_std(output);
        let service = facade
            .serve((tokio::io::stdin(), output))
            .await
            .map_err(io::Error::other)?;
        service.waiting().await.map_err(io::Error::other)?;
        Ok::<(), io::Error>(())
    });
    // The facade, and with it the queue's sender, is gone: the handler's
    // thread ends after the call it is in.
    drop(runtime);
    let _ = worker.join();
    served
}
