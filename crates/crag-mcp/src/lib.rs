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

use std::collections::BTreeMap;
use std::io;
use std::sync::mpsc;

use rmcp::model::{
    BooleanSchema, CallToolRequestParams, CallToolResponse, CallToolResult, ClientResult,
    ElicitRequest, ElicitRequestParams, ElicitationAction, ElicitationSchema,
    GetPromptRequestParams, GetPromptResponse, GetPromptResult, Implementation, ListPromptsResult,
    ListResourceTemplatesResult, ListResourcesResult, ListToolsResult, PaginatedRequestParams,
    PrimitiveSchemaDefinition, Prompt, PromptArgument, PromptMessage, ReadResourceRequestParams,
    ReadResourceResponse, ReadResourceResult, Resource, ResourceContents, ResourceTemplate, Role,
    ServerCapabilities, ServerConfig, ServerRequest, Tool, ToolAnnotations,
};
use rmcp::service::{Peer, RequestContext};
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

/// A prompt as the server advertises it: named instructions an agent
/// loads before a task. The text is computed from the arguments alone,
/// so it lives in the catalog, not the handler.
#[derive(Clone, Debug)]
pub struct PromptSpec {
    pub name: &'static str,
    pub title: &'static str,
    pub description: &'static str,
    /// Each argument: its name, what it is, and whether it is required.
    pub arguments: &'static [(&'static str, &'static str, bool)],
    pub text: fn(&Map<String, Value>) -> String,
}

/// Everything the server offers.
#[derive(Clone, Debug, Default)]
pub struct Catalog {
    pub tools: Vec<ToolSpec>,
    pub resources: Vec<ResourceSpec>,
    pub templates: Vec<TemplateSpec>,
    pub prompts: Vec<PromptSpec>,
}

/// What the user said to a confirmation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decision {
    /// Apply it.
    Yes,
    /// Apply it, and every later change this session, without asking.
    YesToAll,
    No,
    /// Nobody can be asked: the client declared no elicitation support.
    CannotAsk,
}

/// What a tool asks the user mid-call, and where the answer goes.
struct Ask {
    message: String,
    /// Whether to offer "yes to every change this session".
    offer_all: bool,
    answer: mpsc::Sender<Decision>,
}

/// Asks the user through the client, from a tool in the middle of a call
/// (Implementation Plan §11.12.8). The question travels to the protocol
/// thread, which sends an MCP elicitation and waits for the user.
pub struct Confirm {
    asks: tokio::sync::mpsc::UnboundedSender<Ask>,
    can_ask: bool,
}

impl Confirm {
    /// Puts `message` to the user: what they decided. `offer_all` also
    /// offers applying every later change this session without asking.
    pub fn ask(&self, message: &str, offer_all: bool) -> Decision {
        if !self.can_ask {
            return Decision::CannotAsk;
        }
        let (answer, answered) = mpsc::channel();
        let ask = Ask {
            message: message.into(),
            offer_all,
            answer,
        };
        if self.asks.send(ask).is_err() {
            return Decision::No;
        }
        answered.recv().unwrap_or(Decision::No)
    }
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
    fn call(
        &mut self,
        tool: &str,
        args: &Map<String, Value>,
        confirm: &Confirm,
    ) -> Result<Outcome, CallError>;

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
        confirm: Confirm,
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
    prompts: Vec<PromptSpec>,
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
                .enable_prompts()
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
        context: RequestContext<RoleServer>,
    ) -> Result<CallToolResponse, ErrorData> {
        let (answer, mut answered) = tokio::sync::oneshot::channel();
        let (asks, mut asked) = tokio::sync::mpsc::unbounded_channel();
        let can_ask = context
            .peer
            .peer_info()
            .is_some_and(|peer| peer.capabilities.elicitation.is_some());
        let job = Job::Call {
            tool: request.name.to_string(),
            args: request.arguments.unwrap_or_default(),
            confirm: Confirm { asks, can_ask },
            answer,
        };
        self.jobs.send(job).map_err(|_| stopped())?;
        // The tool may ask the user before it answers; both come from the
        // handler's thread, so serving the questions here cannot deadlock.
        let answered = loop {
            tokio::select! {
                answered = &mut answered => break answered,
                ask = asked.recv() => {
                    if let Some(ask) = ask {
                        let _ = ask.answer.send(elicit(&context.peer, &ask).await);
                    }
                }
            }
        };
        match answered.map_err(|_| stopped())? {
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

    async fn list_prompts(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> Result<ListPromptsResult, ErrorData> {
        let prompts = self
            .prompts
            .iter()
            .map(|spec| {
                let arguments = spec
                    .arguments
                    .iter()
                    .map(|(name, description, required)| {
                        PromptArgument::new(*name)
                            .with_description(*description)
                            .with_required(*required)
                    })
                    .collect();
                let mut prompt = Prompt::new(spec.name, Some(spec.description), Some(arguments));
                prompt.title = Some(spec.title.into());
                prompt
            })
            .collect();
        Ok(ListPromptsResult::with_all_items(prompts))
    }

    async fn get_prompt(
        &self,
        request: GetPromptRequestParams,
        _context: RequestContext<RoleServer>,
    ) -> Result<GetPromptResponse, ErrorData> {
        let Some(spec) = self.prompts.iter().find(|p| p.name == request.name) else {
            return Err(ErrorData::invalid_params(
                format!("there is no prompt `{}`", request.name),
                None,
            ));
        };
        let arguments = request.arguments.unwrap_or_default();
        for (name, _, required) in spec.arguments {
            if *required && !arguments.contains_key(*name) {
                return Err(ErrorData::invalid_params(
                    format!("the argument `{name}` is missing"),
                    None,
                ));
            }
        }
        let text = (spec.text)(&arguments);
        let mut result = GetPromptResult::new(vec![PromptMessage::new_text(Role::User, text)]);
        result.description = Some(spec.description.into());
        Ok(result.into())
    }
}

/// Puts an `Ask` to the user as an MCP elicitation: their decision.
async fn elicit(peer: &Peer<RoleServer>, ask: &Ask) -> Decision {
    let mut properties = BTreeMap::new();
    if ask.offer_all {
        properties.insert(
            "always".to_string(),
            PrimitiveSchemaDefinition::Boolean(
                BooleanSchema::new()
                    .description("Yes to every change this session, without asking again"),
            ),
        );
    }
    let params = ElicitRequestParams::FormElicitationParams {
        meta: None,
        message: ask.message.clone(),
        requested_schema: ElicitationSchema::new(properties),
    };
    let request = ServerRequest::ElicitRequest(ElicitRequest::new(params));
    match peer.send_request(request).await {
        Ok(ClientResult::ElicitResult(result)) => match result.action {
            ElicitationAction::Accept => {
                let always = result
                    .content
                    .as_ref()
                    .and_then(|c| c.get("always"))
                    .and_then(Value::as_bool)
                    .unwrap_or(false);
                if always {
                    Decision::YesToAll
                } else {
                    Decision::Yes
                }
            }
            _ => Decision::No,
        },
        // A client that answers wrongly, or not at all, grants nothing.
        _ => Decision::No,
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
                    Job::Call {
                        tool,
                        args,
                        confirm,
                        answer,
                    } => {
                        let _ = answer.send(handler.call(&tool, &args, &confirm));
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
        prompts: catalog.prompts.clone(),
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
