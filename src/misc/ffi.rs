use super::message::*;
use std::ffi::{c_char, CStr};
use std::slice;
use std::sync::Mutex;

pub static MESSAGES: Mutex<Vec<Message>> = Mutex::new(Vec::new());

// Prints messages.
#[no_mangle]
pub extern "C" fn print_messages() {
    println!("{:#?}", MESSAGES);
}

/* private */ unsafe fn extract_str(ptr: *const c_char) -> String {
    assert!(!ptr.is_null());
    let ret = CStr::from_ptr(ptr);
    let ret = String::from_utf8_lossy(ret.to_bytes()).to_string();
    ret
}

/* private */ unsafe fn extract_slice(len: usize, ptr: *const u8) -> Vec<u8> {
    assert!(!ptr.is_null());
    let ret = slice::from_raw_parts(ptr, len);
    let ret = ret.to_owned();
    ret
}

// Inserts a message.
// SAFETY:
//   namespace_ptr is a null-terminated UTF-8 string.
//   uuid_ptr is an array of unsigned bytes of size 0x10 (16).
//   kind_ptr is a null-terminated UTF-8 string.
//   body_len is an unsigned integer.
//   body_ptr is an array of unsigned bytes of size body_len.
// RETURNS: A bool on whether the insert succeeded.
#[no_mangle]
pub extern "C" fn pass_message(
    namespace_ptr: *const c_char,
    uuid_ptr: *const u8,
    kind_ptr: *const c_char,
    body_len: usize,
    body_ptr: *const u8,
) -> bool
{
    assert!(!namespace_ptr.is_null());
    assert!(!uuid_ptr.is_null());
    assert!(!kind_ptr.is_null());
    assert!(!body_ptr.is_null());

    let message = unsafe {
        Message::new(
            extract_str(namespace_ptr),
            extract_slice(0x10, uuid_ptr),
            extract_str(kind_ptr),
            extract_slice(body_len, body_ptr),
        )
    };

    if let Ok(ref mut messages) = MESSAGES.try_lock() {
        messages.push(message);
        true
    } else {
        false
    }
}
