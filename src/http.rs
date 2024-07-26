use bytes::{buf::Reader, Bytes};
use std::sync::{Arc, Condvar, Mutex};

use warp::http;

pub struct HttpListener {
    pub incoming: std::sync::mpsc::Receiver<HttpRequest>,
}

pub struct HttpRequest {
    pub request_data: HttpRequestData,
    pub response: HttpResponse,
}

pub type HttpResponse = Arc<(Mutex<bool>, Mutex<Option<warp::reply::Response>>, Condvar)>;

pub struct HttpRequestData {
    pub method: http::Method,
    pub headers: http::HeaderMap,
    pub path: String,
    pub query: String,
    pub body: Reader<Bytes>,
}
