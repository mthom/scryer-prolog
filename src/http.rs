use std::sync::Arc;
use std::convert::Infallible;

use hyper::{Response, Request, Body};
use tokio::sync::Mutex;
use tokio::sync::mpsc::{channel, Receiver, Sender};

pub struct HttpListener {
    pub incoming: Receiver<HttpRequest>
}

#[derive(Debug)]
pub struct HttpRequest {
    pub request: Request<Body>,
    pub response: HttpResponse,
}

pub type HttpResponse = Sender<Response<Body>>;

pub async fn serve_req(req: Request<Body>, tx: Arc<Mutex<Sender<HttpRequest>>>) -> Result<Response<Body>, Infallible> {
    let (response_tx, mut rx) = channel(1);
    let http_request = HttpRequest { request: req, response: response_tx };
    tx.lock().await.send(http_request).await.unwrap();
    Ok(rx.recv().await.unwrap())
}
