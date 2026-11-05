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
    CallToolRequestParams, CallToolResponse, CallToolResult, Implementation,
    ListResourceTemplatesResult, ListResourcesResult, ListToolsResult, PaginatedRequestParams,
    ReadResourceRequestParams, ReadResourceResponse, ReadResourceResult, Resource,
    ResourceContents, ResourceTemplate, ServerCapabilities, ServerConfig, Tool, ToolAnnotations,
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

/// A resource as the server lists it: a text a client reads by its URI.
#[derive(Clone, Debug)]
pub struct ResourceSpec {
    pub uri: String,
    pub name: String,
    pub title: String,
    pub description: String,
    pub mime_type: &'static str,
}

/// A family of resources whose URIs follow a template, such as
/// `crag://diagnostic/{code}`.
#[derive(Clone, Debug)]
pub struct TemplateSpec {
    pub uri_template: &'static str,
    pub name: &'static str,
    pub title: &'static str,
    pub description: &'static str,
    pub mime_type: &'static str,
}

/// Everything the server offers.
#[derive(Clone, Debug, Default)]
pub struct Catalog {
    pub tools: Vec<ToolSpec>,
    pub resources: Vec<ResourceSpec>,
    pub templates: Vec<TemplateSpec>,
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

/// What answers the calls and reads.
pub trait Handler {
    fn call(&mut self, tool: &str, args: &Map<String, Value>) -> Result<Outcome, CallError>;

    /// The text of the resource at `uri`: `Ok(None)` when there is none,
    /// and `Err` when there is but it cannot be read, with why.
    fn read(&mut self, uri: &str) -> Result<Option<String>, String>;
}

/// The server's name and version, and what it tells a client about itself.
#[derive(Clone, Debug)]
pub struct Info {
    pub name: String,
    pub version: String,
    pub instructions: String,
}

/// A call or a read on its way to the handler's thread, with where its
/// answer goes.
enum Job {
    Call {
        tool: String,
        args: Map<String, Value>,
        answer: tokio::sync::oneshot::Sender<Result<Outcome, CallError>>,
    },
    Read {
        uri: String,
        answer: tokio::sync::oneshot::Sender<Result<Option<String>, String>>,
    },
}

struct Facade {
    info: Info,
    tools: Vec<Tool>,
    resources: Vec<Resource>,
    templates: Vec<ResourceTemplate>,
    /// The type of each listed resource, by URI.
    mime_types: Vec<(String, &'static str)>,
    jobs: mpsc::Sender<Job>,
}

fn resource(spec: &ResourceSpec) -> Resource {
    Resource::new(&spec.uri, &spec.name)
        .with_title(&spec.title)
        .with_description(&spec.description)
        .with_mime_type(spec.mime_type)
}

fn template(spec: &TemplateSpec) -> ResourceTemplate {
    ResourceTemplate::new(spec.uri_template, spec.name)
        .with_title(spec.title)
        .with_description(spec.description)
        .with_mime_type(spec.mime_type)
}

fn stopped() -> ErrorData {
    ErrorData::internal_error("the agent server stopped", None)
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
        ServerConfig::new(
            ServerCapabilities::builder()
                .enable_tools()
                .enable_resources()
                .build(),
        )
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
        let job = Job::Call {
            tool: request.name.to_string(),
            args: request.arguments.unwrap_or_default(),
            answer,
        };
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

    async fn list_resources(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> Result<ListResourcesResult, ErrorData> {
        Ok(ListResourcesResult::with_all_items(self.resources.clone()))
    }

    async fn list_resource_templates(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> Result<ListResourceTemplatesResult, ErrorData> {
        Ok(ListResourceTemplatesResult::with_all_items(
            self.templates.clone(),
        ))
    }

    async fn read_resource(
        &self,
        request: ReadResourceRequestParams,
        _context: RequestContext<RoleServer>,
    ) -> Result<ReadResourceResponse, ErrorData> {
        let (answer, answered) = tokio::sync::oneshot::channel();
        let uri = request.uri;
        let job = Job::Read {
            uri: uri.clone(),
            answer,
        };
        self.jobs.send(job).map_err(|_| stopped())?;
        let found = answered
            .await
            .map_err(|_| stopped())?
            .map_err(|why| ErrorData::internal_error(why, None))?;
        let Some(text) = found else {
            return Err(ErrorData::resource_not_found(
                format!("there is no resource `{uri}`"),
                None,
            ));
        };
        let mime = self
            .mime_types
            .iter()
            .find(|(u, _)| *u == uri)
            .map_or("text/markdown", |(_, m)| m);
        let contents = ResourceContents::text(text, &uri).with_mime_type(mime);
        Ok(ReadResourceResult::new(vec![contents]).into())
    }
}

/// Serves the catalog over standard input and `output` until the input
/// ends. `make` builds the handler on its own thread, so it need not be
/// `Send`.
pub fn serve<H, F>(info: Info, catalog: &Catalog, make: F, output: std::fs::File) -> io::Result<()>
where
    H: Handler,
    F: FnOnce() -> H + Send + 'static,
{
    let (jobs, queue) = mpsc::channel::<Job>();
    let worker = std::thread::Builder::new()
        .name("agent-tools".into())
        .spawn(move || {
            let mut handler = make();
            // A client that went away no longer waits for an answer.
            for job in queue {
                match job {
                    Job::Call { tool, args, answer } => {
                        let _ = answer.send(handler.call(&tool, &args));
                    }
                    Job::Read { uri, answer } => {
                        let _ = answer.send(handler.read(&uri));
                    }
                }
            }
        })?;
    let facade = Facade {
        info,
        tools: catalog.tools.iter().map(tool).collect(),
        resources: catalog.resources.iter().map(resource).collect(),
        templates: catalog.templates.iter().map(template).collect(),
        mime_types: catalog
            .resources
            .iter()
            .map(|r| (r.uri.clone(), r.mime_type))
            .collect(),
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
