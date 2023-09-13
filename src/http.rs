use bytes::Bytes;
use http_body_util::Full;
use hyper::service::Service;
use hyper::{body::Incoming as IncomingBody, Request, Response};
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Condvar, Mutex};

pub struct HttpListener {
    pub incoming: std::sync::mpsc::Receiver<HttpRequest>,
}

#[derive(Debug)]
pub struct HttpRequest {
    pub request: Request<IncomingBody>,
    pub response: HttpResponse,
}

pub type HttpResponse = Arc<(Mutex<bool>, Mutex<Option<Response<Full<Bytes>>>>, Condvar)>;

pub struct HttpService {
    pub tx: std::sync::mpsc::SyncSender<HttpRequest>,
}

impl Service<Request<IncomingBody>> for HttpService {
    type Response = Response<Full<Bytes>>;
    type Error = hyper::Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn call(self: &HttpService, req: Request<IncomingBody>) -> Self::Future {
		// new connection!
		// we send the Request info to Prolog
		let response = Arc::new((Mutex::new(false), Mutex::new(None), Condvar::new()));
		let http_request = HttpRequest { 
            request: req, 
            response: Arc::clone(&response) 
        };
		self.tx.send(http_request).unwrap();

		// we wait for the Response info from Prolog
		{
			let (ready, _response, cvar) = &*response;
			let mut ready = ready.lock().unwrap();
			while !*ready {
			    ready = cvar.wait(ready).unwrap();
			}
		}
		{
			let (_, response, _) = &*response;
			let response = response.lock().unwrap().take();
			let res = response.expect("Data race error in HTTP Server");
			Box::pin(async move {
			Ok(res)
			})
		}
    }
}
