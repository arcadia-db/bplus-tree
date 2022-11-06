#[derive(Debug)]
pub struct Message {
    namespace: String,
    uuid: Vec<u8>,
    kind: String,
    body: Vec<u8>,
}

impl Message {
    pub fn new(namespace: String, uuid: Vec<u8>, kind: String, body: Vec<u8>) -> Self {
        Self { namespace, uuid, kind, body }
    }
}
