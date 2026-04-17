//! Tests for the Reader

#![expect(
    clippy::arithmetic_side_effects,
    clippy::indexing_slicing,
    clippy::unwrap_used,
    reason = "Okay in tests"
)]

use super::*;
use crate::buffer::tests::InterruptOnceReader;
use crate::constants::CHUNK_SIZE;
use std::collections::VecDeque;
use std::io::{self, Cursor, IoSliceMut, Read, Seek, SeekFrom};

// -----------------------------------------------------------------------------
// DynBufReader - Creation
// -----------------------------------------------------------------------------

#[test]
fn test_reader_new() {
    let cur: Cursor<&str> = Cursor::default();
    let reader = DynBufReader::new(cur);

    // Check internal state matches expectations
    assert_eq!(reader.buffer, Buffer::default());
    assert_eq!(reader.max_capacity, DEFAULT_MAX_CAPACITY);
    assert_eq!(reader.reader, Cursor::default());
}

#[test]
fn test_reader_builder() {
    // Create with max_capacity only (initial defaults)
    let cur: Cursor<&str> = Cursor::default();
    let max_capacity = CHUNK_SIZE + 123;
    let reader = DynBufReader::builder(cur)
        .max_capacity(max_capacity)
        .build();

    // Check internal state matches expectations
    assert_eq!(reader.buffer, Buffer::default());
    assert_eq!(reader.max_capacity, 2 * CHUNK_SIZE); // Rounds up
    assert_eq!(reader.reader, Cursor::default());

    // Create with initial_capacity only (max defaults)
    let cur: Cursor<&str> = Cursor::default();
    let initial_capacity = 3 * CHUNK_SIZE;
    let reader = DynBufReader::builder(cur)
        .initial_capacity(initial_capacity)
        .build();

    // Check internal state matches expectations
    assert_eq!(reader.buffer, Buffer::with_capacity(initial_capacity));
    assert_eq!(reader.buffer.cap(), 3 * CHUNK_SIZE);
    assert_eq!(reader.max_capacity, DEFAULT_MAX_CAPACITY);
    assert_eq!(reader.reader, Cursor::default());

    // Create with both initial_capacity and max_capacity
    let cur: Cursor<&str> = Cursor::default();
    let initial_capacity = 4 * CHUNK_SIZE;
    let max_capacity = 8 * CHUNK_SIZE;
    let reader = DynBufReader::builder(cur)
        .initial_capacity(initial_capacity)
        .max_capacity(max_capacity)
        .build();

    // Check internal state matches expectations
    assert_eq!(reader.buffer, Buffer::with_capacity(initial_capacity));
    assert_eq!(reader.buffer.cap(), 4 * CHUNK_SIZE);
    assert_eq!(reader.max_capacity, 8 * CHUNK_SIZE);
    assert_eq!(reader.reader, Cursor::default());

    // Create with max_capacity less than initial_capacity (max is raised to match)
    let cur: Cursor<&str> = Cursor::default();
    let initial_capacity = 8 * CHUNK_SIZE;
    let max_capacity = 2 * CHUNK_SIZE;
    let reader = DynBufReader::builder(cur)
        .initial_capacity(initial_capacity)
        .max_capacity(max_capacity)
        .build();

    // Check internal state matches expectations
    assert_eq!(reader.buffer.cap(), 8 * CHUNK_SIZE);
    assert_eq!(reader.max_capacity, 8 * CHUNK_SIZE); // Raised to match initial
}

// -----------------------------------------------------------------------------
// DynBufReader - Peek Methods
// -----------------------------------------------------------------------------

#[test]
fn test_reader_peek() {
    // Empty reader returns empty slice
    let cur: Cursor<&str> = Cursor::default();
    let reader = DynBufReader::new(cur);
    assert_eq!(reader.peek(5), &[]);

    // With data in the buffer
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    reader.fill_amount(data.len()).unwrap();

    // Peek at fewer bytes than available
    assert_eq!(reader.peek(5), b"Hello");

    // Peek at exactly available bytes
    assert_eq!(reader.peek(data.len()), data.as_bytes());

    // Peek at more than available clamps to what's there
    assert_eq!(reader.peek(100), data.as_bytes());

    // Peek at zero bytes returns empty slice
    assert_eq!(reader.peek(0), &[]);

    // Peek doesn't consume, repeated calls return the same data
    assert_eq!(reader.peek(5), b"Hello");

    // After consuming, peek reflects the new position
    reader.consume(7);
    assert_eq!(reader.peek(5), b"World");
}

#[test]
fn test_reader_peek_behind() {
    // Nothing consumed returns empty slice
    let cur: Cursor<&str> = Cursor::default();
    let reader = DynBufReader::new(cur);
    assert_eq!(reader.peek_behind(5), &[]);

    // With data in the buffer, nothing consumed yet
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    reader.fill_amount(data.len()).unwrap();
    assert_eq!(reader.peek_behind(5), &[]);

    // After consuming some bytes
    reader.consume(7);
    assert_eq!(reader.peek_behind(5), b"llo, ");
    assert_eq!(reader.peek_behind(7), b"Hello, ");

    // More than consumed clamps to what's retained
    assert_eq!(reader.peek_behind(100), b"Hello, ");

    // Zero returns empty
    assert_eq!(reader.peek_behind(0), &[]);

    // Peek behind doesn't change state, repeated calls return the same data
    assert_eq!(reader.peek_behind(7), b"Hello, ");
}

// -----------------------------------------------------------------------------
// impl Read
// -----------------------------------------------------------------------------

#[test]
fn test_reader_read() {
    // Create a reader against no data, for an EOF test
    let cur: Cursor<&'static str> = Cursor::default();
    let mut reader = DynBufReader::new(cur);
    let mut buf = [0u8; 100];
    let len = reader.read(&mut buf).unwrap();

    // We should get nothing
    assert_eq!(len, 0);

    // Create a reader against some data
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    let mut buf = [0u8; 100];
    let len = reader.read(&mut buf).unwrap();

    // The data should all have been read
    assert_eq!(len, data.len());
    assert_eq!(&buf[..len], data.as_bytes());

    // Create a reader against some data again, to read against, multiple times
    let data = "Hello, World!";
    let mut cur = Cursor::new(data);
    cur.set_position(6); // Simulate having already read the first 6 bytes
    let mut reader = DynBufReader::new(cur);
    let mut buf = [0u8; 3];

    // Inject 6 bytes so the first two reads consume buffered data
    reader.buffer.inject_test_data(&data.as_bytes()[..6]); // The 6 bytes we skipped above

    // Read once
    let len = reader.read(&mut buf).unwrap();
    assert_eq!(len, 3);
    assert_eq!(&buf[..len], &data.as_bytes()[..3]);
    assert_eq!(reader.buffer.pos(), 3); // Read 3 from internal buffer

    // Read twice
    let len = reader.read(&mut buf).unwrap();
    assert_eq!(len, 3);
    assert_eq!(&buf[..len], &data.as_bytes()[3..6]);
    assert_eq!(reader.buffer.pos(), 6); // Read another 3 from internal buffer

    // Read thrice
    let len = reader.read(&mut buf).unwrap();
    assert_eq!(len, 3);
    assert_eq!(&buf[..len], &data.as_bytes()[6..9]);
    assert_eq!(reader.buffer.pos(), 0); // Internal buffer was cleared and skipped

    // Read a fourth time
    let len = reader.read(&mut buf).unwrap();
    assert_eq!(len, 3);
    assert_eq!(&buf[..len], &data.as_bytes()[9..12]);

    // And finally read the last bit
    let len = reader.read(&mut buf).unwrap();
    assert_eq!(len, 1);
    assert_eq!(&buf[..len], &data.as_bytes()[12..]);
}

#[test]
fn test_reader_read_vectored() {
    // Create a reader against some data with small target buffers
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    let mut buf1 = [0u8; 5];
    let mut buf2 = [0u8; 10];
    let mut buffers = [IoSliceMut::new(&mut buf1), IoSliceMut::new(&mut buf2)];
    let len = reader.read_vectored(&mut buffers).unwrap();

    // Check that the vectored read did what we'd expect
    assert_eq!(len, data.len());
    assert_eq!(&buf1, &data.as_bytes()[..5]);
    assert_eq!(&buf2[..8], &data.as_bytes()[5..]);
    assert_eq!(reader.buffer.pos(), data.len()); // Confirms fill_buf path

    // Use a large buffer here so `read_vectored` delegates to the inner reader
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    let mut buf = [0u8; CHUNK_SIZE]; // Must be ≥ CHUNK_SIZE to trigger delegation
    let mut buffers = [IoSliceMut::new(&mut buf)];
    let len = reader.read_vectored(&mut buffers).unwrap();

    // Check that the vectored read did what we'd expect
    assert_eq!(len, data.len());
    assert_eq!(&buf[..13], data.as_bytes());
    assert_eq!(reader.buffer.pos(), 0); // Confirms delegation path

    // With partially-consumed buffer, only unconsumed data should be returned
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    reader.fill_amount(data.len()).unwrap();
    reader.consume(7); // Consume "Hello, "

    let mut buf1 = [0u8; 3];
    let mut buf2 = [0u8; 10];
    let mut buffers = [IoSliceMut::new(&mut buf1), IoSliceMut::new(&mut buf2)];
    let len = reader.read_vectored(&mut buffers).unwrap();

    assert_eq!(len, 6);
    assert_eq!(&buf1, b"Wor");
    assert_eq!(&buf2[..3], b"ld!");
}

#[test]
fn test_reader_read_to_end() {
    // Create a reader against some data
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    let mut result = Vec::new();

    // To mirror the test below we need to check that len is 0 before we read
    assert_eq!(reader.buffer.len(), 0); // Confirms internal buffer isn't used
    let len = reader.read_to_end(&mut result).unwrap();

    // We should have read everything without touching the internal buffer
    assert_eq!(len, data.len());
    assert_eq!(result, data.as_bytes());
    assert_eq!(reader.buffer.len(), 0); // Should still be 0

    // Create another reader with some data pre-injected
    let data = "Hello, World!";
    let mut cur = Cursor::new(data);
    cur.set_position(7); // Simulate having already read the first 7 bytes
    let mut reader = DynBufReader::new(cur);
    let mut result = Vec::new();

    // Pre-inject some data into the internal buffer
    reader.buffer.inject_test_data(&data.as_bytes()[..7]); // The 7 bytes we skipped above
    assert_eq!(reader.buffer.len(), 7); // Confirms internal buffer usage

    // Read the rest of the data
    let len = reader.read_to_end(&mut result).unwrap();

    // We should get buffered data and cursor data
    assert_eq!(len, data.len());
    assert_eq!(result, data.as_bytes());
    assert_eq!(reader.buffer.len(), 0); // Confirms the buffer was cleared
}

#[test]
fn test_reader_read_to_string() {
    // Create a reader against some UTF-8 data
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    let mut result = String::new();
    let len = reader.read_to_string(&mut result).unwrap();

    // Reading should work fine
    assert_eq!(len, data.len());
    assert_eq!(result, data);

    // Create a reader against some non-UTF-8 data
    let data = vec![0xFF, 0xFE, 0xFD]; // Invalid UTF-8
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    let mut result = String::new();
    let err = reader.read_to_string(&mut result).unwrap_err();

    // We should get an invalid data error
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);

    // Non-empty String + valid UTF-8 reader → content appended (Path B)
    let cur = Cursor::new("World!");
    let mut reader = DynBufReader::new(cur);
    let mut result = String::from("Hello, ");
    let len = reader.read_to_string(&mut result).unwrap();

    assert_eq!(len, 6);
    assert_eq!(result, "Hello, World!");

    // Non-empty String + invalid UTF-8 → error, original content preserved (Path B)
    let data = vec![0xFF, 0xFE, 0xFD]; // Invalid UTF-8
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    let mut result = String::from("keep me");
    let err = reader.read_to_string(&mut result).unwrap_err();

    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert_eq!(result, "keep me"); // Original content preserved
}

#[test]
fn test_reader_read_exact() {
    // Create a reader against some data and try reading more than that
    let data = "Hi";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    let mut buf = [0u8; 10];
    let err = reader.read_exact(&mut buf).unwrap_err();

    // Trying to read more than we have should fail with an EOF error
    assert_eq!(err.kind(), io::ErrorKind::UnexpectedEof);

    // Create a reader against some data again
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);

    // To mirror the test below we need to check that len is 0 before we read
    assert_eq!(reader.buffer.len(), 0); // Confirms internal buffer isn't used
    let mut buf = [0u8; 5];
    reader.read_exact(&mut buf).unwrap();

    // We should get exactly the size we requested
    assert_eq!(&buf, &data.as_bytes()[..5]);

    // Once more, create a reader against some data with some pre-injected
    let data = "Hello, World!";
    let mut cur = Cursor::new(data);
    cur.set_position(7); // Simulate having already read the first 7 bytes
    let mut reader = DynBufReader::new(cur);

    // Pre-inject some data into the internal buffer
    reader.buffer.inject_test_data(&data.as_bytes()[..7]); // The 7 bytes we skipped above
    assert_eq!(reader.buffer.len(), 7); // Confirms internal buffer usage

    // Request 13 bytes - more than buffered (7), forcing slow path
    let mut buf = [0u8; 13];
    reader.read_exact(&mut buf).unwrap();

    // Should successfully read all 13 bytes across buffer + inner reader
    assert_eq!(&buf, b"Hello, World!");
    assert_eq!(reader.buffer.len(), 0); // Confirms the buffer was cleared

    // Interrupted retry, reader returns Interrupted once, then succeeds
    let inner = Cursor::new(b"Hello, World!");
    let reader = InterruptOnceReader {
        inner,
        interrupted: false,
    };
    let mut reader = DynBufReader::new(reader);
    let mut buf = [0u8; 13];
    reader.read_exact(&mut buf).unwrap();

    assert_eq!(&buf, b"Hello, World!");
}

// -----------------------------------------------------------------------------
// impl BufRead
// -----------------------------------------------------------------------------

#[test]
fn test_reader_bufread_fill_buf() {
    // Create a reader against some data
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);

    // We should get all of the data
    assert_eq!(reader.buffer.len(), 0); // Buffer is empty at first
    let read = reader.fill_buf().unwrap();
    assert_eq!(read, data.as_bytes());
    assert_eq!(reader.buffer.len(), data.len()); // Buffer has all the data after

    // Reading again should give the already read data
    let read = reader.fill_buf().unwrap();
    assert_eq!(read, data.as_bytes());

    // Consume a bit and read again, we should get the unconsumed bit
    reader.consume(7);
    let read = reader.fill_buf().unwrap();
    assert_eq!(read, &data.as_bytes()[7..]);
    assert_eq!(reader.buffer.len(), data.len()); // The buffer hasn't changed yet

    // Reading after all data is consumed should give nothing
    reader.consume(data.len() - 7);
    let read = reader.fill_buf().unwrap();
    assert_eq!(read, &[]);
}

/* Note: There is no test for `consume` as it's just a wrapper over `Buffer::consume()`
 * So testing is deferred to the buffers tests
 * There's no need to test this method twice after all
 */

// -----------------------------------------------------------------------------
// DynBufReader - Fill Methods
// -----------------------------------------------------------------------------

#[test]
fn test_reader_fill_amount() {
    // Basic: read a specific amount from a reader with enough data
    let data = vec![0u8; 3 * CHUNK_SIZE];
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    let bytes_read = reader.fill_amount(3 * CHUNK_SIZE).unwrap();

    assert!(bytes_read >= 3 * CHUNK_SIZE);
    assert!(reader.buffer.len() >= 3 * CHUNK_SIZE);

    // EOF: request more bytes than available
    let data = b"short";
    let cur = Cursor::new(data.as_slice());
    let mut reader = DynBufReader::new(cur);
    let bytes_read = reader.fill_amount(1000).unwrap();

    assert_eq!(bytes_read, 5);
    assert_eq!(reader.buffer.len(), 5);

    // Exceeds max_capacity: should return an error
    let data = vec![0u8; 4 * CHUNK_SIZE];
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::builder(cur)
        .max_capacity(2 * CHUNK_SIZE)
        .build();
    let err = reader.fill_amount(3 * CHUNK_SIZE).unwrap_err();

    assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
}

#[test]
fn test_reader_fill_exact() {
    // Basic: read exactly N bytes
    let data = vec![42u8; 100];
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    reader.fill_exact(100).unwrap();

    assert_eq!(reader.buffer.len(), 100);
    assert!(reader.buffer.buf().iter().all(|&b| b == 42));

    // EOF: request more than available
    let data = b"short";
    let cur = Cursor::new(data.as_slice());
    let mut reader = DynBufReader::new(cur);
    let err = reader.fill_exact(1000).unwrap_err();

    assert_eq!(err.kind(), io::ErrorKind::UnexpectedEof);

    // Exceeds max_capacity: should return an error
    let data = vec![0u8; 4 * CHUNK_SIZE];
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::builder(cur)
        .max_capacity(2 * CHUNK_SIZE)
        .build();
    let err = reader.fill_exact(3 * CHUNK_SIZE).unwrap_err();

    assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
}

#[test]
fn test_reader_fill_to_end() {
    // Basic: read all data from a small reader
    let data = vec![42u8; 100];
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    let bytes_read = reader.fill_to_end().unwrap();

    assert_eq!(bytes_read, 100);
    assert_eq!(reader.buffer.len(), 100);

    // Empty reader
    let cur: Cursor<&[u8]> = Cursor::new(b"");
    let mut reader = DynBufReader::new(cur);
    let bytes_read = reader.fill_to_end().unwrap();

    assert_eq!(bytes_read, 0);

    // Capped: data larger than max_capacity, reading should stop at the cap
    let data = vec![0u8; 4 * CHUNK_SIZE];
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::builder(cur)
        .max_capacity(2 * CHUNK_SIZE)
        .build();
    let bytes_read = reader.fill_to_end().unwrap();

    // Should have read up to the cap, not all data
    assert_eq!(reader.buffer.cap(), 2 * CHUNK_SIZE);
    assert!(bytes_read <= 2 * CHUNK_SIZE);
    assert!(reader.buffer.len() <= 2 * CHUNK_SIZE);
}

#[test]
fn test_reader_fill_until() {
    // Delimiter found
    let cur = Cursor::new(b"key=value\nother".as_slice());
    let mut reader = DynBufReader::new(cur);
    let bytes_read = reader.fill_until(b'\n').unwrap();

    assert!(bytes_read > 0);
    assert!(reader.buffer.buf()[..reader.buffer.len()].contains(&b'\n'));

    // Delimiter not found, EOF
    let cur = Cursor::new(b"no newline here".as_slice());
    let mut reader = DynBufReader::new(cur);
    let bytes_read = reader.fill_until(b'\n').unwrap();

    assert_eq!(bytes_read, 15);
    assert!(!reader.buffer.buf()[..reader.buffer.len()].contains(&b'\n'));

    // Delimiter not found, capped
    let data = vec![b'x'; 4 * CHUNK_SIZE];
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::builder(cur)
        .max_capacity(2 * CHUNK_SIZE)
        .build();
    let bytes_read = reader.fill_until(b'\n').unwrap();

    assert!(bytes_read <= 2 * CHUNK_SIZE);
    assert!(reader.buffer.len() <= 2 * CHUNK_SIZE);
}

#[test]
fn test_reader_fill_until_char() {
    // Delimiter found (multi-byte UTF-8)
    let cur = Cursor::new("Hello, 世界!".as_bytes());
    let mut reader = DynBufReader::new(cur);
    let bytes_read = reader.fill_until_char('界').unwrap();

    assert!(bytes_read > 0);

    // Delimiter not found, EOF
    let cur = Cursor::new("no match".as_bytes());
    let mut reader = DynBufReader::new(cur);
    let bytes_read = reader.fill_until_char('界').unwrap();

    assert_eq!(bytes_read, 8);

    // Delimiter not found, capped
    let data = "x".repeat(4 * CHUNK_SIZE);
    let cur = Cursor::new(data.as_bytes().to_vec());
    let mut reader = DynBufReader::builder(cur)
        .max_capacity(2 * CHUNK_SIZE)
        .build();
    let bytes_read = reader.fill_until_char('界').unwrap();

    assert!(bytes_read <= 2 * CHUNK_SIZE);
}

#[test]
fn test_reader_fill_until_str() {
    // Needle found
    let cur = Cursor::new(b"Hello, World!END more data".as_slice());
    let mut reader = DynBufReader::new(cur);
    let bytes_read = reader.fill_until_str("END").unwrap();

    assert!(bytes_read > 0);

    // Needle not found, EOF
    let cur = Cursor::new(b"no match here".as_slice());
    let mut reader = DynBufReader::new(cur);
    let bytes_read = reader.fill_until_str("END").unwrap();

    assert_eq!(bytes_read, 13);

    // Needle not found, capped
    let data = vec![b'x'; 4 * CHUNK_SIZE];
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::builder(cur)
        .max_capacity(2 * CHUNK_SIZE)
        .build();
    let bytes_read = reader.fill_until_str("END").unwrap();

    assert!(bytes_read <= 2 * CHUNK_SIZE);

    // Empty needle returns immediately
    let cur = Cursor::new(b"anything".as_slice());
    let mut reader = DynBufReader::new(cur);
    let bytes_read = reader.fill_until_str("").unwrap();

    assert_eq!(bytes_read, 0);
}

// -----------------------------------------------------------------------------
// DynBufReader - Accessor Methods
// -----------------------------------------------------------------------------

#[test]
fn test_reader_get_ref() {
    let cur = Cursor::new("Hello");
    let reader = DynBufReader::new(cur);

    // get_ref should return the inner reader
    let inner: &Cursor<&str> = reader.get_ref();
    assert_eq!(inner.position(), 0);
}

#[test]
fn test_reader_get_mut() {
    let cur = Cursor::new("Hello");
    let mut reader = DynBufReader::new(cur);

    // get_mut should allow mutating the inner reader
    reader.get_mut().set_position(3);
    assert_eq!(reader.get_ref().position(), 3);
}

#[test]
#[expect(
    clippy::as_conversions,
    reason = "test-only usize→u64 that cannot overflow"
)]
fn test_reader_into_inner() {
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);

    // Fill the buffer, the cursor advances past all data
    reader.fill_amount(data.len()).unwrap();

    // Recover the inner reader
    let (inner, _) = reader.into_parts();
    assert_eq!(inner.position(), data.len() as u64);
}

#[test]
fn test_reader_max_capacity() {
    // Default max capacity
    let cur: Cursor<&str> = Cursor::default();
    let reader = DynBufReader::new(cur);
    assert_eq!(reader.max_capacity(), DEFAULT_MAX_CAPACITY);

    // Custom max capacity
    let cur: Cursor<&str> = Cursor::default();
    let reader = DynBufReader::builder(cur)
        .max_capacity(4 * CHUNK_SIZE)
        .build();
    assert_eq!(reader.max_capacity(), 4 * CHUNK_SIZE);
}

// -----------------------------------------------------------------------------
// DynBufReader - Debug
// -----------------------------------------------------------------------------

#[test]
fn test_reader_debug() {
    let cur = Cursor::new("Hello");
    let reader = DynBufReader::new(cur);
    let debug = format!("{reader:?}");

    // Should contain the struct name and the delegated sub-struct
    assert!(debug.contains("DynBufReader"));
    assert!(debug.contains("reader"));
    assert!(debug.contains("max_capacity"));
    assert!(debug.contains("buffer: Buffer { pos: 0, len: 0"));

    // With data in the buffer, pos and len should reflect the fill.
    let cur = Cursor::new("Hello, World!");
    let mut reader = DynBufReader::new(cur);
    reader.fill_amount(13).unwrap();
    let debug = format!("{reader:?}");
    assert!(debug.contains("buffer: Buffer { pos: 0, len: 13"));

    // After consuming some data, pos should move and len should stay put.
    reader.consume(5);
    let debug = format!("{reader:?}");
    assert!(debug.contains("buffer: Buffer { pos: 5, len: 13"));
}

// -----------------------------------------------------------------------------
// DynBufReader - Seek
// -----------------------------------------------------------------------------

#[test]
fn test_reader_seek_start() {
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);

    // Fill and consume some data
    reader.fill_amount(data.len()).unwrap();
    reader.consume(5);
    assert_eq!(reader.buffer.len(), data.len());

    // Seek to start should invalidate the buffer
    let pos = reader.seek(SeekFrom::Start(0)).unwrap();
    assert_eq!(pos, 0);
    assert_eq!(reader.buffer.len(), 0);
}

#[test]
#[expect(
    clippy::as_conversions,
    reason = "test-only usize→u64 that cannot overflow"
)]
fn test_reader_seek_end() {
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);

    // Fill data
    reader.fill_amount(data.len()).unwrap();
    assert_eq!(reader.buffer.len(), data.len());

    // Seek to end should invalidate the buffer
    let pos = reader.seek(SeekFrom::End(0)).unwrap();
    assert_eq!(pos, data.len() as u64);
    assert_eq!(reader.buffer.len(), 0);
}

#[test]
fn test_reader_seek_current() {
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);

    // Fill and consume some data
    reader.fill_amount(data.len()).unwrap();
    reader.consume(5);

    // Seek forward from current, adjusts for unconsumed bytes
    let pos = reader.seek(SeekFrom::Current(2)).unwrap();
    assert_eq!(pos, 7); // Logical position was 5, +2 = 7
    assert_eq!(reader.buffer.len(), 0); // Buffer invalidated

    // Read to verify we're at the right position
    let mut buf = [0u8; 6];
    reader.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"World!");

    // Overflow: i64::MIN with unconsumed data would overflow in checked_sub → InvalidInput
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    reader.fill_amount(data.len()).unwrap();

    let err = reader.seek(SeekFrom::Current(i64::MIN)).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
}

#[test]
fn test_reader_seek_current_backward() {
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);

    // Read all data, then seek backward
    reader.fill_amount(data.len()).unwrap();
    reader.consume(data.len());

    let pos = reader.seek(SeekFrom::Current(-6)).unwrap();
    assert_eq!(pos, 7);
    assert_eq!(reader.buffer.len(), 0); // Buffer invalidated

    // Read to verify position
    let mut buf = [0u8; 6];
    reader.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"World!");
}

// -----------------------------------------------------------------------------
// DynBufReader - seek_relative
// -----------------------------------------------------------------------------

#[test]
fn test_reader_seek_relative() {
    // Forward within unconsumed data, no I/O, just advances pos
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    reader.fill_amount(data.len()).unwrap();
    assert_eq!(reader.buffer.pos(), 0);

    reader.seek_relative(5).unwrap();
    assert_eq!(reader.buffer.pos(), 5);
    assert_eq!(reader.buffer.len(), data.len()); // Buffer NOT invalidated
    assert_eq!(reader.peek(8), b", World!");

    // Backward within retained consumed data, no I/O
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    reader.fill_amount(data.len()).unwrap();
    reader.consume(7);
    assert_eq!(reader.buffer.pos(), 7);

    reader.seek_relative(-5).unwrap();
    assert_eq!(reader.buffer.pos(), 2);
    assert_eq!(reader.buffer.len(), data.len()); // Buffer NOT invalidated
    assert_eq!(reader.peek(5), b"llo, ");

    // Forward beyond buffered data, falls through to inner seek
    let data = "Hello, World!";
    let mut cur = Cursor::new(data);
    cur.set_position(5); // Simulate having read 5 bytes already
    let mut reader = DynBufReader::new(cur);
    reader.buffer.inject_test_data(&data.as_bytes()[..5]);
    reader.consume(3); // Logical position is 3, unconsumed = 2

    reader.seek_relative(8).unwrap();
    assert_eq!(reader.buffer.len(), 0); // Buffer invalidated
    let mut buf = [0u8; 2];
    reader.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"d!"); // Logical was 3, +8 = 11

    // Backward beyond retained consumed data, falls through to inner seek
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    reader.fill_amount(data.len()).unwrap();
    reader.consume(10);
    reader.compact(); // Drop retained consumed data
    assert_eq!(reader.buffer.pos(), 0);
    reader.consume(1);
    assert_eq!(reader.buffer.pos(), 1);

    // Only 1 byte retained, seeking back by 2 exceeds it → fallback
    // Logical pos is 11, seek by -2 → logical 9
    reader.seek_relative(-2).unwrap();
    assert_eq!(reader.buffer.len(), 0); // Buffer invalidated
    let mut buf = [0u8; 4];
    reader.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"rld!");

    // Zero offset, in-buffer fast path, no-op
    let data = "Hello, World!";
    let cur = Cursor::new(data);
    let mut reader = DynBufReader::new(cur);
    reader.fill_amount(data.len()).unwrap();
    reader.consume(5);

    reader.seek_relative(0).unwrap();
    assert_eq!(reader.buffer.pos(), 5);
    assert_eq!(reader.buffer.len(), data.len()); // Buffer NOT invalidated
}

// --- Codex: ------------------------------------------------------------------

struct ScriptedReader {
    steps: VecDeque<io::Result<Vec<u8>>>,
}

impl ScriptedReader {
    fn new(steps: impl IntoIterator<Item = io::Result<Vec<u8>>>) -> Self {
        Self {
            steps: steps.into_iter().collect(),
        }
    }
}

impl Read for ScriptedReader {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let Some(step) = self.steps.pop_front() else {
            return Ok(0);
        };

        match step {
            Ok(bytes) => {
                let bytes_read = bytes.len().min(buf.len());
                buf[..bytes_read].copy_from_slice(&bytes[..bytes_read]);

                if bytes_read < bytes.len() {
                    self.steps.push_front(Ok(bytes[bytes_read..].to_vec()));
                }

                Ok(bytes_read)
            }
            Err(error) => Err(error),
        }
    }
}

fn patterned_bytes(len: usize) -> Vec<u8> {
    (0..len)
        .map(|index| b'a' + u8::try_from(index % 26).unwrap())
        .collect()
}

// -----------------------------------------------------------------------------
// DynBufReader - Debug
// -----------------------------------------------------------------------------

#[test]
fn test_codex_reader_debug() {
    // Start with an empty reader so the format is easy to spot-check.
    let reader = DynBufReader::new(Cursor::new("Hello"));
    let debug = format!("{reader:?}");

    // The debug output should name the type and delegate to the buffer's own Debug.
    assert!(debug.contains("DynBufReader"));
    assert!(debug.contains("reader"));
    assert!(debug.contains("max_capacity"));
    assert!(debug.contains("buffer: Buffer { pos: 0, len: 0"));

    // Fill some data so the len is non-zero.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    let debug = format!("{reader:?}");
    assert!(debug.contains("buffer: Buffer { pos: 0, len: 13"));

    // Consume a few bytes so the buffer's pos advances.
    reader.consume(5);
    let debug = format!("{reader:?}");
    assert!(debug.contains("buffer: Buffer { pos: 5, len: 13"));
}

// -----------------------------------------------------------------------------
// DynBufReader - Creation
// -----------------------------------------------------------------------------

#[test]
fn test_codex_reader_new() {
    // Build a reader with the defaults so we can inspect the initial state.
    let reader = DynBufReader::new(Cursor::<&str>::default());

    // The reader should start with a default buffer and default cap.
    assert_eq!(reader.buffer, Buffer::default());
    assert_eq!(reader.max_capacity, DEFAULT_MAX_CAPACITY);
    assert_eq!(reader.reader, Cursor::default());
}

#[test]
fn test_codex_reader_builder() {
    // Start with only a custom max capacity.
    let reader = DynBufReader::builder(Cursor::<&str>::default())
        .max_capacity(CHUNK_SIZE + 123)
        .build();

    // The max should round up, while the initial buffer stays at the default size.
    assert_eq!(reader.buffer, Buffer::default());
    assert_eq!(reader.max_capacity, 2 * CHUNK_SIZE);

    // Now only customize the initial capacity.
    let reader = DynBufReader::builder(Cursor::<&str>::default())
        .initial_capacity(3 * CHUNK_SIZE)
        .build();

    // The buffer should honor the requested starting size.
    assert_eq!(reader.buffer, Buffer::with_capacity(3 * CHUNK_SIZE));
    assert_eq!(reader.max_capacity, DEFAULT_MAX_CAPACITY);

    // Finally, set both values with max already large enough.
    let reader = DynBufReader::builder(Cursor::<&str>::default())
        .initial_capacity(4 * CHUNK_SIZE)
        .max_capacity(8 * CHUNK_SIZE)
        .build();

    // Both values should be preserved after builder normalization.
    assert_eq!(reader.buffer.cap(), 4 * CHUNK_SIZE);
    assert_eq!(reader.max_capacity, 8 * CHUNK_SIZE);

    // If max is too small, the builder should raise it to the initial capacity.
    let reader = DynBufReader::builder(Cursor::<&str>::default())
        .initial_capacity(8 * CHUNK_SIZE)
        .max_capacity(2 * CHUNK_SIZE)
        .build();

    // This keeps the reader internally consistent without shrinking the buffer.
    assert_eq!(reader.buffer.cap(), 8 * CHUNK_SIZE);
    assert_eq!(reader.max_capacity, 8 * CHUNK_SIZE);
}

#[test]
fn test_codex_reader_into_inner() {
    // Fill some data first so the inner cursor has definitely advanced.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();

    // Taking the inner reader should give us the advanced cursor back.
    let (inner, _) = reader.into_parts();
    assert_eq!(
        inner.position(),
        u64::try_from("Hello, World!".len()).unwrap()
    );
}

#[test]
fn test_codex_reader_get_ref() {
    // Start at the beginning of a simple cursor.
    let reader = DynBufReader::new(Cursor::new("Hello"));

    // A shared reference should expose the inner cursor as-is.
    let inner: &Cursor<&str> = reader.get_ref();
    assert_eq!(inner.position(), 0);
}

#[test]
fn test_codex_reader_get_mut() {
    // Start with a mutable reader so we can push on the inner cursor directly.
    let mut reader = DynBufReader::new(Cursor::new("Hello"));

    // Mutating through the inner handle should affect future reads.
    reader.get_mut().set_position(3);
    assert_eq!(reader.get_ref().position(), 3);
}

#[test]
fn test_codex_reader_max_capacity() {
    // The default constructor should use the crate-level default max.
    let reader = DynBufReader::new(Cursor::<&str>::default());
    assert_eq!(reader.max_capacity(), DEFAULT_MAX_CAPACITY);

    // The builder should expose a custom max exactly once normalized.
    let reader = DynBufReader::builder(Cursor::<&str>::default())
        .max_capacity(4 * CHUNK_SIZE)
        .build();
    assert_eq!(reader.max_capacity(), 4 * CHUNK_SIZE);
}

// -----------------------------------------------------------------------------
// DynBufReader - Peek Methods
// -----------------------------------------------------------------------------

#[test]
fn test_codex_reader_peek() {
    // An empty reader should have nothing to show.
    let reader = DynBufReader::new(Cursor::<&str>::default());
    assert_eq!(reader.peek(5), &[]);

    // Fill a small payload so we can read from the unconsumed window.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();

    // Peeking less than the available bytes should clamp to the request.
    assert_eq!(reader.peek(5), b"Hello");

    // Peeking the exact size should give us the whole unconsumed slice.
    assert_eq!(reader.peek(13), b"Hello, World!");

    // Peeking too far should clamp to what is actually buffered.
    assert_eq!(reader.peek(100), b"Hello, World!");

    // Peeking zero bytes should always be empty.
    assert_eq!(reader.peek(0), &[]);

    // Consuming should shift the visible window forward.
    reader.consume(7);
    assert_eq!(reader.peek(5), b"World");
}

#[test]
fn test_codex_reader_peek_behind() {
    // Before anything is consumed, there is no retained prefix to inspect.
    let reader = DynBufReader::new(Cursor::<&str>::default());
    assert_eq!(reader.peek_behind(5), &[]);

    // Fill a payload so we can move the logical cursor through it.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    assert_eq!(reader.peek_behind(5), &[]);

    // After consuming, lookbehind should expose the retained prefix.
    reader.consume(7);
    assert_eq!(reader.peek_behind(5), b"llo, ");
    assert_eq!(reader.peek_behind(7), b"Hello, ");

    // Asking for more than was consumed should clamp to the retained bytes.
    assert_eq!(reader.peek_behind(100), b"Hello, ");

    // Asking for zero should stay empty just like `peek`.
    assert_eq!(reader.peek_behind(0), &[]);
}

// -----------------------------------------------------------------------------
// DynBufReader - Fill Methods
// -----------------------------------------------------------------------------

#[test]
fn test_codex_reader_fill() {
    // First, show that `fill` performs one append into existing spare capacity.
    let mut reader = DynBufReader::new(ScriptedReader::new([
        Ok(b"abc".to_vec()),
        Ok(b"def".to_vec()),
    ]));
    assert_eq!(reader.fill().unwrap(), 3);
    reader.consume(2);
    let prefix = reader.peek_behind(2).to_vec();
    assert_eq!(reader.fill().unwrap(), 3);

    // The newly-read bytes should append, and the retained prefix should survive.
    assert_eq!(reader.buffer(), b"abcdef");
    assert_eq!(reader.peek_behind(2), prefix.as_slice());

    // Next, fill the entire current capacity so a later call has no room to use.
    let mut reader = DynBufReader::builder(ScriptedReader::new([
        Ok(patterned_bytes(CHUNK_SIZE)),
        Ok(b"later".to_vec()),
    ]))
    .initial_capacity(CHUNK_SIZE)
    .build();
    assert_eq!(reader.fill().unwrap(), CHUNK_SIZE);
    assert_eq!(reader.fill().unwrap(), 0);

    // A zero with `len == cap` means the buffer was already full.
    assert_eq!(reader.buffer.len(), reader.buffer.cap());

    // Finally, leave spare capacity but no input so EOF is the only explanation.
    let mut reader = DynBufReader::new(ScriptedReader::new(Vec::<io::Result<Vec<u8>>>::new()));
    assert_eq!(reader.fill().unwrap(), 0);

    // Here `len < cap`, so the zero came from EOF instead of a full buffer.
    assert!(reader.buffer.len() < reader.buffer.cap());
}

#[test]
fn test_codex_reader_fill_while() {
    // Start with a controlled two-step reader so we can preserve lookbehind across a fill.
    let mut reader = DynBufReader::new(ScriptedReader::new([
        Ok(b"abc".to_vec()),
        Ok(b"def".to_vec()),
    ]));
    reader.fill().unwrap();
    reader.consume(2);
    let prefix = reader.peek_behind(2).to_vec();
    let read = reader.fill_while(|buf| buf.len() < 4).unwrap();

    // The second chunk should append and keep the consumed prefix intact.
    assert_eq!(read, 3);
    assert_eq!(reader.buffer(), b"abcdef");
    assert_eq!(reader.peek_behind(2), prefix.as_slice());

    // Now seed a newline so the predicate is already false before any I/O happens.
    let mut reader = DynBufReader::new(Cursor::new(b"line\nrest".as_slice()));
    reader.fill_until(b'\n').unwrap();
    let len_before = reader.buffer.len();
    let read = reader.fill_while(|buf| !buf.contains(&b'\n')).unwrap();

    // A zero with unchanged length means the request was already satisfied.
    assert_eq!(read, 0);
    assert_eq!(reader.buffer.len(), len_before);

    // Next, read to EOF without ever satisfying the predicate.
    let mut reader = DynBufReader::new(Cursor::new(b"unterminated".as_slice()));
    assert_eq!(
        reader.fill_while(|buf| !buf.contains(&b'\n')).unwrap(),
        b"unterminated".len()
    );
    let read = reader.fill_while(|buf| !buf.contains(&b'\n')).unwrap();

    // A zero while there is still room to grow means EOF.
    assert_eq!(read, 0);
    assert!(reader.buffer.len() < reader.max_capacity());

    // Finally, hit the configured max and call again with the predicate still unsatisfied.
    let mut reader = DynBufReader::builder(Cursor::new(patterned_bytes(2 * CHUNK_SIZE)))
        .max_capacity(CHUNK_SIZE)
        .build();
    assert_eq!(
        reader.fill_while(|buf| !buf.contains(&b'\n')).unwrap(),
        CHUNK_SIZE
    );
    let read = reader.fill_while(|buf| !buf.contains(&b'\n')).unwrap();

    // A zero at `max_capacity` is the indirect signal that the cap stopped us.
    assert_eq!(read, 0);
    assert_eq!(reader.buffer.len(), reader.max_capacity());
}

#[test]
fn test_codex_reader_fill_amount() {
    // Read an exact amount from a source with plenty of data.
    let mut reader = DynBufReader::new(Cursor::new(patterned_bytes(3 * CHUNK_SIZE)));
    let read = reader.fill_amount(3 * CHUNK_SIZE).unwrap();

    // `fill_amount` should return how many bytes actually landed in the buffer.
    assert_eq!(read, 3 * CHUNK_SIZE);
    assert_eq!(reader.buffer.len(), 3 * CHUNK_SIZE);

    // If the reader runs out first, we should get the shorter count instead of an error.
    let mut reader = DynBufReader::new(Cursor::new(b"short".to_vec()));
    let read = reader.fill_amount(1000).unwrap();
    assert_eq!(read, 5);
    assert_eq!(reader.buffer.len(), 5);

    // Fill part of the cap, then consume some bytes so we have a retained prefix to preserve.
    let mut reader = DynBufReader::builder(ScriptedReader::new([
        Ok(patterned_bytes(CHUNK_SIZE + 128)),
        Ok(patterned_bytes(CHUNK_SIZE - 128)),
    ]))
    .max_capacity(2 * CHUNK_SIZE)
    .build();
    reader.fill_amount(CHUNK_SIZE + 128).unwrap();
    reader.consume(128);
    let prefix = reader.peek_behind(128).to_vec();
    let read = reader.fill_amount(CHUNK_SIZE).unwrap();

    // The request should clamp to the remaining room instead of erroring.
    assert_eq!(read, CHUNK_SIZE - 128);
    assert_eq!(reader.buffer.len(), 2 * CHUNK_SIZE);
    assert_eq!(reader.peek_behind(128), prefix.as_slice());

    // Interrupted reads should be retried just like they are in the buffer itself.
    let inner = Cursor::new(b"Hello, World!");
    let scripted = InterruptOnceReader {
        inner,
        interrupted: false,
    };
    let mut reader = DynBufReader::new(scripted);
    let read = reader.fill_amount(13).unwrap();
    assert_eq!(read, 13);
    assert_eq!(reader.buffer(), b"Hello, World!");
}

#[test]
fn test_codex_reader_fill_exact() {
    // Start with a simple success case that appends while preserving lookbehind.
    let mut reader = DynBufReader::new(Cursor::new(b"abcdefghi".to_vec()));
    reader.fill_exact(6).unwrap();
    reader.consume(2);
    let prefix = reader.peek_behind(2).to_vec();
    reader.fill_exact(3).unwrap();

    // The reader should now hold the full payload, with the consumed prefix untouched.
    assert_eq!(reader.buffer(), b"abcdefghi");
    assert_eq!(reader.peek_behind(2), prefix.as_slice());

    // If EOF arrives before the full request, the call should fail hard.
    let mut reader = DynBufReader::new(Cursor::new(b"short".to_vec()));
    let err = reader.fill_exact(1000).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::UnexpectedEof);

    // Now hit the max-capacity guard without compacting away a retained prefix first.
    let mut reader = DynBufReader::builder(Cursor::new(patterned_bytes(3 * CHUNK_SIZE)))
        .max_capacity(2 * CHUNK_SIZE)
        .build();
    reader.fill_exact(CHUNK_SIZE + 128).unwrap();
    reader.consume(128);
    let len_before = reader.buffer.len();
    let pos_before = reader.buffer.pos();
    let prefix = reader.peek_behind(128).to_vec();
    let err = reader.fill_exact(CHUNK_SIZE).unwrap_err();

    // This should fail with guidance instead of silently compacting for us.
    assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
    assert!(err.to_string().contains("compact()"));
    assert_eq!(reader.buffer.len(), len_before);
    assert_eq!(reader.buffer.pos(), pos_before);
    assert_eq!(reader.peek_behind(128), prefix.as_slice());

    // Once we compact explicitly, the exact same request should fit.
    reader.compact();
    reader.fill_exact(CHUNK_SIZE).unwrap();
    assert_eq!(reader.buffer.len(), 2 * CHUNK_SIZE);
    assert_eq!(reader.buffer.pos(), 0);
}

#[test]
fn test_codex_reader_fill_to_end() {
    // Read an entire small payload into the managed buffer.
    let mut reader = DynBufReader::new(Cursor::new(vec![42u8; 100]));
    let read = reader.fill_to_end().unwrap();
    assert_eq!(read, 100);
    assert_eq!(reader.buffer.len(), 100);

    // An empty reader should stay empty and report zero.
    let mut reader = DynBufReader::new(Cursor::new(Vec::<u8>::new()));
    let read = reader.fill_to_end().unwrap();
    assert_eq!(read, 0);
    assert!(reader.buffer.is_empty());

    // If the configured max is smaller than the source, stop cleanly at the cap.
    let mut reader = DynBufReader::builder(Cursor::new(patterned_bytes(4 * CHUNK_SIZE)))
        .max_capacity(2 * CHUNK_SIZE)
        .build();
    let read = reader.fill_to_end().unwrap();
    assert_eq!(read, 2 * CHUNK_SIZE);
    assert_eq!(reader.buffer.len(), 2 * CHUNK_SIZE);

    // Finally, prove that type-level fills keep the retained prefix alive.
    let data = patterned_bytes(2 * CHUNK_SIZE);
    let mut reader = DynBufReader::new(ScriptedReader::new([
        Ok(data[..16].to_vec()),
        Ok(data[16..].to_vec()),
    ]));
    reader.fill_amount(16).unwrap();
    reader.consume(4);
    let prefix = reader.peek_behind(4).to_vec();
    let read = reader.fill_to_end().unwrap();

    // We should append the remaining bytes without losing lookbehind.
    assert_eq!(read, data.len() - 16);
    assert_eq!(reader.buffer(), data.as_slice());
    assert_eq!(reader.peek_behind(4), prefix.as_slice());
}

#[test]
fn test_codex_reader_fill_until() {
    // Split the delimiter across reads so we exercise the incremental scan path.
    let mut reader = DynBufReader::new(ScriptedReader::new([
        Ok(b"key=va".to_vec()),
        Ok(b"lue\nother".to_vec()),
    ]));
    let read = reader.fill_until(b'\n').unwrap();

    // The method should stop once the newline becomes visible.
    assert!(read > 0);
    assert!(reader.buffer().contains(&b'\n'));

    // If no delimiter ever appears, the method should finish at EOF.
    let mut reader = DynBufReader::new(Cursor::new(b"no newline here".to_vec()));
    let read = reader.fill_until(b'\n').unwrap();
    assert_eq!(read, 15);
    assert!(!reader.buffer().contains(&b'\n'));

    // If the max is smaller than the stream, stop at the configured cap.
    let mut reader = DynBufReader::builder(Cursor::new(vec![b'x'; 4 * CHUNK_SIZE]))
        .max_capacity(2 * CHUNK_SIZE)
        .build();
    let read = reader.fill_until(b'\n').unwrap();
    assert_eq!(read, 2 * CHUNK_SIZE);
    assert_eq!(reader.buffer.len(), 2 * CHUNK_SIZE);

    // Type-level delimiter fills should still preserve lookbehind between calls.
    let mut reader = DynBufReader::new(Cursor::new(b"key=value\nother".to_vec()));
    reader.fill_until(b'=').unwrap();
    reader.consume(4);
    let prefix = reader.peek_behind(4).to_vec();
    reader.fill_until(b'\n').unwrap();
    assert_eq!(reader.peek_behind(4), prefix.as_slice());
}

#[test]
fn test_codex_reader_fill_until_char() {
    // Split a multi-byte UTF-8 character across reads to prove boundary handling.
    let mut reader = DynBufReader::new(ScriptedReader::new([
        Ok(vec![b'H', b'e', b'l', b'l', b'o', b',', b' ', 0xE4, 0xB8]),
        Ok(vec![0x96, 0xE7, 0x95, 0x8C, b'!']),
    ]));
    let read = reader.fill_until_char('世').unwrap();

    // The first completed `世` should stop the read even though it spanned two chunks.
    assert!(read > 0);
    assert!(reader.buffer.as_str().unwrap().contains('世'));

    // EOF without a match should just return the number of bytes read.
    let mut reader = DynBufReader::new(Cursor::new("no match".as_bytes().to_vec()));
    let read = reader.fill_until_char('界').unwrap();
    assert_eq!(read, 8);

    // A small max should cap the search without producing an error.
    let mut reader = DynBufReader::builder(Cursor::new(vec![b'x'; 4 * CHUNK_SIZE]))
        .max_capacity(2 * CHUNK_SIZE)
        .build();
    let read = reader.fill_until_char('界').unwrap();
    assert_eq!(read, 2 * CHUNK_SIZE);

    // Like the other type-level fills, this one should preserve consumed prefix bytes.
    let mut reader = DynBufReader::new(Cursor::new("ab世cd界ef".as_bytes().to_vec()));
    reader.fill_until_char('世').unwrap();
    reader.consume(2);
    let prefix = reader.peek_behind(2).to_vec();
    reader.fill_until_char('界').unwrap();
    assert_eq!(reader.peek_behind(2), prefix.as_slice());
}

#[test]
fn test_codex_reader_fill_until_str() {
    // Split the needle across reads so the overlap logic has real work to do.
    let mut reader = DynBufReader::new(ScriptedReader::new([
        Ok(b"Hello, World!E".to_vec()),
        Ok(b"ND more data".to_vec()),
    ]));
    let read = reader.fill_until_str("END").unwrap();

    // The search should stop as soon as the cross-boundary match appears.
    assert!(read > 0);
    assert!(reader.buffer.as_str().unwrap().contains("END"));

    // If the needle never appears, EOF should end the search cleanly.
    let mut reader = DynBufReader::new(Cursor::new(b"no match here".to_vec()));
    let read = reader.fill_until_str("END").unwrap();
    assert_eq!(read, 13);

    // If the configured max is smaller than the input, stop there instead.
    let mut reader = DynBufReader::builder(Cursor::new(vec![b'x'; 4 * CHUNK_SIZE]))
        .max_capacity(2 * CHUNK_SIZE)
        .build();
    let read = reader.fill_until_str("END").unwrap();
    assert_eq!(read, 2 * CHUNK_SIZE);

    // An empty needle is a no-op by design.
    let mut reader = DynBufReader::new(Cursor::new(b"anything".to_vec()));
    assert_eq!(reader.fill_until_str("").unwrap(), 0);

    // Retained lookbehind should survive across repeated string searches too.
    let mut reader = DynBufReader::new(Cursor::new(b"abc123ENDtail".to_vec()));
    reader.fill_until_str("123").unwrap();
    reader.consume(3);
    let prefix = reader.peek_behind(3).to_vec();
    reader.fill_until_str("END").unwrap();
    assert_eq!(reader.peek_behind(3), prefix.as_slice());
}

// -----------------------------------------------------------------------------
// impl Read
// -----------------------------------------------------------------------------

#[test]
fn test_codex_reader_read() {
    // A fresh reader with no buffered data should delegate straight to the inner reader.
    let mut reader = DynBufReader::new(Cursor::<&str>::default());
    let mut buf = [0u8; 16];
    let read = reader.read(&mut buf).unwrap();
    assert_eq!(read, 0);

    // With a real payload, the same direct path should still produce bytes.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    let read = reader.read(&mut buf).unwrap();
    assert_eq!(read, 13);
    assert_eq!(&buf[..read], b"Hello, World!");
    assert_eq!(reader.buffer.len(), 0);

    // Seed buffered data so the read comes from the managed buffer first.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    let mut small = [0u8; 5];
    let read = reader.read(&mut small).unwrap();
    assert_eq!(read, 5);
    assert_eq!(&small, b"Hello");
    assert_eq!(reader.buffer.pos(), 5);

    // Once the buffer is exhausted, `read` should clear lookbehind and delegate again.
    let mut reader = DynBufReader::new(ScriptedReader::new([
        Ok(b"Hello".to_vec()),
        Ok(b", World!".to_vec()),
    ]));
    reader.fill_amount(5).unwrap();
    reader.consume(5);
    assert_eq!(reader.peek_behind(5), b"Hello");
    let mut buf = [0u8; 3];
    let read = reader.read(&mut buf).unwrap();
    assert_eq!(read, 3);
    assert_eq!(&buf, b", W");
    assert_eq!(reader.peek_behind(5), &[]);
}

#[test]
fn test_codex_reader_read_vectored() {
    // Small destination buffers should read through the buffered window.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    let mut first = [0u8; 5];
    let mut second = [0u8; 10];
    let mut buffers = [IoSliceMut::new(&mut first), IoSliceMut::new(&mut second)];
    let read = reader.read_vectored(&mut buffers).unwrap();

    // The vectored read should stitch the bytes across both slices.
    assert_eq!(read, 13);
    assert_eq!(&first, b"Hello");
    assert_eq!(&second[..8], b", World!");
    assert_eq!(reader.buffer.pos(), 13);

    // Large targets on an exhausted buffer should delegate straight to the inner reader.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    let mut big = [0u8; CHUNK_SIZE];
    let mut buffers = [IoSliceMut::new(&mut big)];
    let read = reader.read_vectored(&mut buffers).unwrap();
    assert_eq!(read, 13);
    assert_eq!(&big[..13], b"Hello, World!");
    assert_eq!(reader.buffer.len(), 0);

    // That exhausted delegation path should also wipe retained lookbehind.
    let mut reader = DynBufReader::new(ScriptedReader::new([
        Ok(b"Hello".to_vec()),
        Ok(b", World!".to_vec()),
    ]));
    reader.fill_amount(5).unwrap();
    reader.consume(5);
    assert_eq!(reader.peek_behind(5), b"Hello");
    let mut big = [0u8; CHUNK_SIZE];
    let mut buffers = [IoSliceMut::new(&mut big)];
    let read = reader.read_vectored(&mut buffers).unwrap();
    assert_eq!(read, 8);
    assert_eq!(&big[..8], b", World!");
    assert_eq!(reader.peek_behind(5), &[]);
}

#[test]
fn test_codex_reader_read_to_end() {
    // With an empty internal buffer, the reader should just stream everything through.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    let mut out = Vec::new();
    let read = reader.read_to_end(&mut out).unwrap();
    assert_eq!(read, 13);
    assert_eq!(out, b"Hello, World!");
    assert_eq!(reader.buffer.len(), 0);

    // If we already buffered part of the stream, `read_to_end` should prepend it.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(7).unwrap();
    let mut out = Vec::new();
    let read = reader.read_to_end(&mut out).unwrap();
    assert_eq!(read, 13);
    assert_eq!(out, b"Hello, World!");
    assert_eq!(reader.buffer.len(), 0);

    // And because this is a std-trait surface, exhausting it should drop lookbehind.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(7).unwrap();
    reader.consume(3);
    assert_eq!(reader.peek_behind(3), b"Hel");
    let mut out = Vec::new();
    let read = reader.read_to_end(&mut out).unwrap();
    assert_eq!(read, 10);
    assert_eq!(out, b"lo, World!");
    assert_eq!(reader.peek_behind(3), &[]);
}

#[test]
fn test_codex_reader_read_to_string() {
    // Valid UTF-8 should append into an empty string.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    let mut out = String::new();
    let read = reader.read_to_string(&mut out).unwrap();
    assert_eq!(read, 13);
    assert_eq!(out, "Hello, World!");

    // Invalid UTF-8 should fail without changing the destination.
    let mut reader = DynBufReader::new(Cursor::new(vec![0xFF, 0xFE, 0xFD]));
    let mut out = String::new();
    let err = reader.read_to_string(&mut out).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    assert_eq!(out, "");

    // A non-empty string should still append on success.
    let mut reader = DynBufReader::new(Cursor::new("World!"));
    let mut out = String::from("Hello, ");
    let read = reader.read_to_string(&mut out).unwrap();
    assert_eq!(read, 6);
    assert_eq!(out, "Hello, World!");

    // An I/O error after valid UTF-8 should roll the empty-string path back completely.
    let mut reader = DynBufReader::new(ScriptedReader::new([
        Ok(b"abc".to_vec()),
        Err(io::Error::other("boom")),
    ]));
    let mut out = String::new();
    let err = reader.read_to_string(&mut out).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::Other);
    assert_eq!(out, "");

    // The non-empty-string path should also preserve its original contents on error.
    let mut reader = DynBufReader::new(ScriptedReader::new([
        Ok(b"abc".to_vec()),
        Err(io::Error::other("boom")),
    ]));
    let mut out = String::from("keep me");
    let err = reader.read_to_string(&mut out).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::Other);
    assert_eq!(out, "keep me");
}

#[test]
fn test_codex_reader_read_exact() {
    // If enough data is already buffered, `read_exact` should use the fast path.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    let mut buf = [0u8; 5];
    reader.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"Hello");
    assert_eq!(reader.buffer.pos(), 5);

    // If the request crosses the buffer boundary, the method should keep going through `read`.
    let mut reader = DynBufReader::new(ScriptedReader::new([
        Ok(b"Hello, ".to_vec()),
        Ok(b"World!".to_vec()),
    ]));
    reader.fill_amount(7).unwrap();
    let mut buf = [0u8; 13];
    reader.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"Hello, World!");
    assert_eq!(reader.buffer.len(), 0);

    // A short source should still surface `UnexpectedEof`.
    let mut reader = DynBufReader::new(Cursor::new("Hi"));
    let mut buf = [0u8; 10];
    let err = reader.read_exact(&mut buf).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::UnexpectedEof);

    // Interrupted reads should be retried until the request finishes.
    let inner = Cursor::new(b"Hello, World!");
    let scripted = InterruptOnceReader {
        inner,
        interrupted: false,
    };
    let mut reader = DynBufReader::new(scripted);
    let mut buf = [0u8; 13];
    reader.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"Hello, World!");
}

// -----------------------------------------------------------------------------
// impl BufRead
// -----------------------------------------------------------------------------

#[test]
fn test_codex_reader_fill_buf() {
    // Start with a two-chunk payload so we can observe the exhausted-refill behavior.
    let data = patterned_bytes(2 * CHUNK_SIZE);
    let mut reader = DynBufReader::new(Cursor::new(data.clone()));
    let first = reader.fill_buf().unwrap().to_vec();

    // The initial fill should expose the first buffered window.
    assert_eq!(first, data[..CHUNK_SIZE].to_vec());
    assert_eq!(reader.buffer.len(), CHUNK_SIZE);

    // Calling again without consuming should hand back the same window.
    let second = reader.fill_buf().unwrap().to_vec();
    assert_eq!(second, first);

    // Consuming part of the window should shift the returned slice forward.
    reader.consume(7);
    let tail = reader.fill_buf().unwrap().to_vec();
    assert_eq!(tail, data[7..CHUNK_SIZE].to_vec());

    // Once the window is exhausted, `fill_buf` should clear retained bytes before refilling.
    reader.consume(CHUNK_SIZE - 7);
    assert!(!reader.peek_behind(5).is_empty());
    let next = reader.fill_buf().unwrap().to_vec();
    assert_eq!(next, data[CHUNK_SIZE..].to_vec());
    assert_eq!(reader.peek_behind(5), &[]);
}

#[test]
fn test_codex_reader_consume() {
    // Fill a small payload so `consume` has something to move across.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();

    // Consuming a small amount should advance by exactly that much.
    reader.consume(2);
    assert_eq!(reader.buffer.pos(), 2);

    // Consuming past the end should clamp instead of overflowing.
    reader.consume(100);
    assert_eq!(reader.buffer.pos(), 13);
}

// -----------------------------------------------------------------------------
// impl DynBufRead
// -----------------------------------------------------------------------------

#[test]
fn test_codex_reader_capacity() {
    // Use a custom initial capacity so the answer is easy to distinguish.
    let reader = DynBufReader::builder(Cursor::<&str>::default())
        .initial_capacity(3 * CHUNK_SIZE)
        .build();

    // The DynBufRead view should report the current buffer capacity.
    assert_eq!(reader.capacity(), 3 * CHUNK_SIZE);
}

#[test]
fn test_codex_reader_buffer() {
    // Fill and consume so the buffer contains both consumed and unconsumed data.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    reader.consume(7);

    // `buffer()` should return the retained contents, not just the live suffix.
    assert_eq!(reader.buffer(), b"Hello, World!");
}

#[test]
fn test_codex_reader_pos() {
    // Move the logical cursor into the buffer.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    reader.consume(7);

    // `pos()` should report where the live window begins.
    assert_eq!(reader.pos(), 7);
}

#[test]
fn test_codex_reader_shrink() {
    // Start oversized so a shrink has visible work to do.
    let mut reader = DynBufReader::builder(Cursor::new("Hello"))
        .initial_capacity(4 * CHUNK_SIZE)
        .build();
    reader.fill_amount(5).unwrap();

    // Shrinking should keep the data while releasing spare capacity.
    reader.shrink();
    assert_eq!(reader.capacity(), CHUNK_SIZE);
    assert_eq!(reader.buffer(), b"Hello");
}

#[test]
fn test_codex_reader_compact() {
    // Fill and consume so there is a real retained prefix to drop.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    reader.consume(7);

    // Compacting should move the live suffix to the front.
    reader.compact();
    assert_eq!(reader.pos(), 0);
    assert_eq!(reader.buffer(), b"World!");
}

#[test]
fn test_codex_reader_clear() {
    // Fill and consume so there is state to reset.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    reader.consume(7);
    let cap = reader.capacity();

    // Clearing should forget the data without giving capacity back.
    reader.clear();
    assert_eq!(reader.pos(), 0);
    assert_eq!(reader.buffer(), &[]);
    assert_eq!(reader.capacity(), cap);
}

#[test]
fn test_codex_reader_discard() {
    // Start with extra capacity so discard can prove it shrinks too.
    let mut reader = DynBufReader::builder(Cursor::new("Hello, World!"))
        .initial_capacity(4 * CHUNK_SIZE)
        .build();
    reader.fill_amount(13).unwrap();
    reader.consume(7);

    // Discarding should clear the data and return to the minimum size.
    reader.discard();
    assert_eq!(reader.pos(), 0);
    assert_eq!(reader.buffer(), &[]);
    assert_eq!(reader.capacity(), CHUNK_SIZE);
}

#[test]
fn test_codex_reader_dyn_buf_read_fill() {
    // Call the trait method explicitly so we know that surface still works.
    let mut reader = DynBufReader::new(ScriptedReader::new([Ok(b"abc".to_vec())]));
    let read = DynBufRead::fill(&mut reader).unwrap();

    // The trait and inherent versions should agree on the byte count and buffer state.
    assert_eq!(read, 3);
    assert_eq!(reader.buffer(), b"abc");
}

#[test]
fn test_codex_reader_dyn_buf_read_fill_while() {
    // Call the trait method explicitly with a delimiter predicate.
    let mut reader = DynBufReader::new(Cursor::new(b"abc\n".to_vec()));
    let read = DynBufRead::fill_while(&mut reader, |buf| !buf.contains(&b'\n')).unwrap();

    // The trait path should use the same reader behavior as the inherent wrapper.
    assert_eq!(read, 4);
    assert_eq!(reader.buffer(), b"abc\n");
}

// -----------------------------------------------------------------------------
// DynBufReader - Seek
// -----------------------------------------------------------------------------

#[test]
fn test_codex_reader_seek() {
    // Seek from the start should invalidate any buffered state.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    reader.consume(5);
    let pos = reader.seek(SeekFrom::Start(0)).unwrap();
    assert_eq!(pos, 0);
    assert_eq!(reader.buffer.len(), 0);

    // Seek from the end should do the same and land at the stream length.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    let pos = reader.seek(SeekFrom::End(0)).unwrap();
    assert_eq!(pos, u64::try_from("Hello, World!".len()).unwrap());
    assert_eq!(reader.buffer.len(), 0);

    // SeekFrom::Current must account for unconsumed bytes still sitting in the buffer.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    reader.consume(5);
    let pos = reader.seek(SeekFrom::Current(2)).unwrap();
    assert_eq!(pos, 7);
    assert_eq!(reader.buffer.len(), 0);
    let mut buf = [0u8; 6];
    reader.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"World!");

    // Negative current seeks should work too once we have advanced the logical cursor.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    reader.consume(13);
    let pos = reader.seek(SeekFrom::Current(-6)).unwrap();
    assert_eq!(pos, 7);
    assert_eq!(reader.buffer.len(), 0);

    // And the checked arithmetic should reject impossible offsets instead of wrapping.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    let err = reader.seek(SeekFrom::Current(i64::MIN)).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidInput);
}

#[test]
fn test_codex_reader_seek_relative() {
    // A forward seek inside the buffered window should just advance `pos`.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    reader.seek_relative(5).unwrap();
    assert_eq!(reader.buffer.pos(), 5);
    assert_eq!(reader.peek(8), b", World!");

    // A backward seek inside retained lookbehind should unconsume without I/O.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    reader.consume(7);
    reader.seek_relative(-5).unwrap();
    assert_eq!(reader.buffer.pos(), 2);
    assert_eq!(reader.peek(5), b"llo, ");

    // A forward seek past the buffered window should fall back to `Seek::seek`.
    let mut cursor = Cursor::new("Hello, World!");
    cursor.set_position(5);
    let mut reader = DynBufReader::new(cursor);
    reader.buffer.inject_test_data(&"Hello".as_bytes()[..5]);
    reader.consume(3);
    reader.seek_relative(8).unwrap();
    assert_eq!(reader.buffer.len(), 0);
    let mut buf = [0u8; 2];
    reader.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"d!");

    // A backward seek past retained lookbehind should also invalidate the buffer.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    reader.consume(10);
    reader.compact();
    reader.consume(1);
    reader.seek_relative(-2).unwrap();
    assert_eq!(reader.buffer.len(), 0);
    let mut buf = [0u8; 4];
    reader.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"rld!");

    // A zero offset should be a cheap no-op when we already have the bytes buffered.
    let mut reader = DynBufReader::new(Cursor::new("Hello, World!"));
    reader.fill_amount(13).unwrap();
    reader.consume(5);
    reader.seek_relative(0).unwrap();
    assert_eq!(reader.buffer.pos(), 5);
    assert_eq!(reader.buffer.len(), 13);
}

#[test]
fn test_fill_amount_never_exceeds_max_capacity() {
    // Pins the invariant that after any `fill_amount` the backing `Buffer`'s capacity is
    // still `<= max_capacity`. The reader's pre-check passes when
    // `amt + buffer.len() <= max_capacity`, after which `Buffer::fill_amount` grows via
    // `cap_up_linear(len + amt)`. Since `max_capacity` is a CHUNK_SIZE multiple and
    // `max_capacity >= len + amt`, `cap_up_linear(len + amt) <= max_capacity` — so the
    // grown cap cannot overshoot. Same reasoning applies to `fill_exact`.

    let src = vec![0xA5u8; 8 * CHUNK_SIZE];

    // Case 1: empty buffer, amt = max_capacity exactly.
    let max_cap = 4 * CHUNK_SIZE;
    let mut reader = DynBufReader::builder(Cursor::new(src.clone()))
        .max_capacity(max_cap)
        .build();
    reader.fill_amount(max_cap).unwrap();
    assert!(
        reader.buffer.cap() <= max_cap,
        "case 1: cap={} exceeded max_capacity={}",
        reader.buffer.cap(),
        max_cap,
    );

    // Case 2: pre-fill to a non-aligned length, then fill the exact remainder.
    let mut reader = DynBufReader::builder(Cursor::new(src.clone()))
        .max_capacity(max_cap)
        .build();
    reader.fill_exact(CHUNK_SIZE + 123).unwrap();
    assert_eq!(reader.buffer.len(), CHUNK_SIZE + 123);
    let remainder = max_cap - reader.buffer.len();
    reader.fill_amount(remainder).unwrap();
    assert!(
        reader.buffer.cap() <= max_cap,
        "case 2: cap={} exceeded max_capacity={}",
        reader.buffer.cap(),
        max_cap,
    );

    // Case 3: len = 1, amt = max_cap - 1 — the pre-check allows this at the boundary.
    let mut reader = DynBufReader::builder(Cursor::new(src.clone()))
        .max_capacity(max_cap)
        .build();
    reader.fill_exact(1).unwrap();
    reader.fill_amount(max_cap - 1).unwrap();
    assert!(
        reader.buffer.cap() <= max_cap,
        "case 3: cap={} exceeded max_capacity={}",
        reader.buffer.cap(),
        max_cap,
    );

    // Case 4: max_capacity at the CHUNK_SIZE floor.
    let mut reader = DynBufReader::builder(Cursor::new(src.clone()))
        .max_capacity(CHUNK_SIZE)
        .build();
    reader.fill_amount(CHUNK_SIZE).unwrap();
    assert!(
        reader.buffer.cap() <= CHUNK_SIZE,
        "case 4: cap={} exceeded max_capacity={}",
        reader.buffer.cap(),
        CHUNK_SIZE,
    );

    // Case 5: non-power-of-two max_capacity, via initial_capacity raising it.
    // `.max_capacity(x)` alone rounds via `Buffer::cap_up` (power-of-two), but the
    // builder's `.max(buffer.cap())` can land on any CHUNK_SIZE multiple — here 3x.
    let mut reader = DynBufReader::builder(Cursor::new(src.clone()))
        .initial_capacity(3 * CHUNK_SIZE)
        .max_capacity(CHUNK_SIZE)
        .build();
    assert_eq!(reader.max_capacity(), 3 * CHUNK_SIZE);
    reader.fill_amount(3 * CHUNK_SIZE).unwrap();
    assert!(
        reader.buffer.cap() <= 3 * CHUNK_SIZE,
        "case 5: cap={} exceeded max_capacity={}",
        reader.buffer.cap(),
        3 * CHUNK_SIZE,
    );

    // Case 6: chained fills in mixed-size increments up to the cap.
    let mut reader = DynBufReader::builder(Cursor::new(src.clone()))
        .max_capacity(max_cap)
        .build();
    for step in [1usize, CHUNK_SIZE - 1, CHUNK_SIZE + 5, 1, 42] {
        let room = max_cap - reader.buffer.len();
        if step > room {
            break;
        }
        reader.fill_exact(step).unwrap();
        assert!(
            reader.buffer.cap() <= max_cap,
            "case 6 step={step}: cap={} exceeded max_capacity={}",
            reader.buffer.cap(),
            max_cap,
        );
    }
    let remainder = max_cap - reader.buffer.len();
    reader.fill_amount(remainder).unwrap();
    assert_eq!(reader.buffer.len(), max_cap);
    assert!(
        reader.buffer.cap() <= max_cap,
        "case 6 final: cap={} exceeded max_capacity={}",
        reader.buffer.cap(),
        max_cap,
    );
}
