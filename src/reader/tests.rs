//! Tests for the Reader
//!
//! These tests are in the same narrative order as the main file, and are designed to not depend on
//! things that we've yet to have written tests for, at least narratively. While the test runner is
//! asynchronous and this does not matter there, when reading the file, it makes the flow much
//! easier to understand since we don't introduce future concepts if we can avoid them.

#![expect(
    clippy::arithmetic_side_effects,
    clippy::indexing_slicing,
    clippy::unwrap_used,
    reason = "Okay in tests"
)]

use super::*;
use crate::constants::CHUNK_SIZE;
use std::io::{Cursor, IoSliceMut, Read};

// -----------------------------------------------------------------------------
// DynBufReader - Creation
// -----------------------------------------------------------------------------

#[test]
fn test_reader_new() {
    let cur: Cursor<&str> = Cursor::default();
    let reader = DynBufReader::new(cur);

    // Check internal state matches expectations
    assert_eq!(reader.buffer, Buffer::default());
    assert_eq!(reader.max_capacity, DEFAULT_MAX_SIZE);
    assert_eq!(reader.reader, Cursor::default());
}

#[test]
fn test_reader_with_max_capacity() {
    let cur: Cursor<&str> = Cursor::default();
    let max_capacity = CHUNK_SIZE + 123;
    let reader = DynBufReader::with_max_capacity(max_capacity, cur);

    // Check internal state matches expectations
    assert_eq!(reader.buffer, Buffer::default());
    assert_eq!(reader.max_capacity, 2 * CHUNK_SIZE); // Rounds up
    assert_eq!(reader.reader, Cursor::default());
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

    // Inject exactly 6 bytes into the internal buffer such
    // that the first two reads will consume from there
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

    // Again, create a reader against some data, this time with a large buffer
    // so we hit the code-path delegating to the given buffers reader instead
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
}

// -----------------------------------------------------------------------------
// impl BufRead
// -----------------------------------------------------------------------------

// -----------------------------------------------------------------------------
// TODO
// -----------------------------------------------------------------------------

// -----------------------------------------------------------------------------
// TODO
// -----------------------------------------------------------------------------

// -----------------------------------------------------------------------------
// OLD:
// -----------------------------------------------------------------------------
/*
mod impl_bufread {
    use std::io::Cursor;

    use super::*;

    #[test]
    fn old_test_fill_buf() {
        let data = "Hello, World!";
        let cur = Cursor::new(data);
        let mut reader = DynBufReader::new(cur);

        // Compare filled data matches
        let filled = reader.fill_buf().unwrap();

        assert_eq!(filled, data.as_bytes());
    }

    #[test]
    fn old_test_fill_buf_multiple_times() {
        let data = "Hello, World!";
        let cur = Cursor::new(data);
        let mut reader = DynBufReader::new(cur);

        // First segment
        let filled = reader.fill_buf().unwrap();

        assert_eq!(filled, data.as_bytes());

        reader.consume(5);

        // Second segment
        let filled = reader.fill_buf().unwrap();

        assert_eq!(filled, &data.as_bytes()[5..]);

        reader.consume(5);

        // Third segment
        let filled = reader.fill_buf().unwrap();

        assert_eq!(filled, &data.as_bytes()[10..]);

        reader.consume(3);

        // EOF
        let filled = reader.fill_buf().unwrap();

        assert_eq!(filled, b"");
    }

    #[test]
    fn old_test_fill_buf_empty() {
        let data = "";
        let cur = Cursor::new(data);
        let mut reader = DynBufReader::new(cur);

        let filled = reader.fill_buf().unwrap();

        assert_eq!(filled, data.as_bytes());
    }

    /*
    #[test]
    fn old_test_fill_buf_respects_max_capacity() {
        todo!();
    }

    #[test]
    fn old_test_fill_buf_grows() {
        todo!();
    }
    */
}

// TODO: Add useful tests and not just LLM vomit.

// Claude generated tests below: -------------------------------------------
/*

#[test]
fn old_test_llm_fill_buf_empty() {
    let data = b"";
    let mut reader = DynBufReader::new(Cursor::new(data));

    let buf = reader.fill_buf().unwrap();
    assert_eq!(buf, b"");
}

#[test]
fn old_test_llm_fill_buf_grows_when_full() {
    // Create data larger than initial chunk size to force growth
    let data = vec![b'A'; CHUNK_SIZE + 100];
    let mut reader = DynBufReader::new(Cursor::new(data.clone()));

    // First fill - buffer should grow to accommodate all data
    let buf = reader.fill_buf().unwrap();
    let initial_len = buf.len();
    assert!(buf.len() >= CHUNK_SIZE, "Should read at least CHUNK_SIZE");
    assert!(buf.iter().all(|&b| b == b'A'));

    // Verify that buffer actually grew if needed
    if initial_len < data.len() {
        // Consume what we have
        reader.consume(initial_len);

        // Second fill should get remaining data
        let buf = reader.fill_buf().unwrap();
        assert_eq!(
            buf.len(),
            data.len() - initial_len,
            "Should read remaining data"
        );
        assert!(buf.iter().all(|&b| b == b'A'));

        // Verify we got all data across both fills
        assert_eq!(
            initial_len + buf.len(),
            data.len(),
            "Should have read all data total"
        );
    } else {
        // All data was read in first fill - buffer grew successfully
        assert_eq!(
            initial_len,
            data.len(),
            "Should read all data in first fill when buffer grows"
        );
    }
}

#[test]
fn old_test_llm_fill_buf_with_consume_cycle() {
    // Test the consume-and-refill cycle with larger data
    // This is different from previous test because it verifies the cycle works correctly
    let data = vec![b'B'; CHUNK_SIZE * 2];
    let mut reader = DynBufReader::new(Cursor::new(data));

    // First fill
    let buf = reader.fill_buf().unwrap();
    assert!(
        buf.len() >= CHUNK_SIZE,
        "First fill should read at least CHUNK_SIZE"
    );
    let first_len = buf.len();

    // Consume everything from first fill
    reader.consume(first_len);

    // Second fill should get remaining data (if any)
    let buf = reader.fill_buf().unwrap();
    let second_len = buf.len();

    if first_len < CHUNK_SIZE * 2 {
        assert!(second_len > 0, "Should have remaining data to read");
        assert_eq!(
            first_len + second_len,
            CHUNK_SIZE * 2,
            "Total should equal data size"
        );
    } else {
        assert_eq!(second_len, 0, "Should be at EOF after reading all data");
    }
}

#[test]
fn old_test_llm_fill_buf_consume_zero() {
    let data = b"Hello";
    let mut reader = DynBufReader::new(Cursor::new(data));

    let buf = reader.fill_buf().unwrap();
    assert_eq!(buf, b"Hello");

    reader.consume(0);

    let buf = reader.fill_buf().unwrap();
    assert_eq!(buf, b"Hello");
}

#[test]
fn old_test_llm_fill_buf_consume_beyond_available() {
    let data = b"Hello";
    let mut reader = DynBufReader::new(Cursor::new(data));

    let buf = reader.fill_buf().unwrap();
    assert_eq!(buf, b"Hello");

    // Consume more than available (should clamp)
    reader.consume(1000);

    let buf = reader.fill_buf().unwrap();
    assert_eq!(buf, b"");
}

#[test]
fn old_test_llm_fill_buf_eof_after_consume() {
    // Test that fill_buf correctly returns empty slice at EOF
    let data = b"Hello, World!";
    let mut reader = DynBufReader::new(Cursor::new(data));

    // Fill buffer
    let buf = reader.fill_buf().unwrap();
    assert_eq!(buf, b"Hello, World!");

    // Consume all data
    reader.consume(13);

    // fill_buf should attempt to refill but return empty (EOF reached)TODO
    let buf = reader.fill_buf().unwrap();
    assert_eq!(buf, b"", "Should return empty slice at EOF");
}

#[test]
fn old_test_llm_fill_buf_respects_max_capacity() {
    let data = vec![0u8; CHUNK_SIZE * 4];
    let mut reader = DynBufReader::with_max_capacity(CHUNK_SIZE * 2, Cursor::new(data));

    // First fill should read up to max_capacity
    let buf = reader.fill_buf().unwrap();
    let first_len = buf.len();
    assert!(
        first_len <= CHUNK_SIZE * 2,
        "Should not exceed max_capacity"
    );

    // Verify buffer capacity doesn't exceed max_capacity
    assert!(
        reader.buffer.cap() <= CHUNK_SIZE * 2,
        "Buffer capacity should not exceed max_capacity"
    );

    // Consume and fill again to verify max_capacity is consistently enforced
    reader.consume(first_len);
    let buf = reader.fill_buf().unwrap();
    assert!(
        buf.len() <= CHUNK_SIZE * 2,
        "Should still respect max_capacity on refill"
    );
    assert!(
        reader.buffer.cap() <= CHUNK_SIZE * 2,
        "Buffer capacity should still not exceed max_capacity"
    );
}

// ========== Integration tests (Read + BufRead) ==========

#[test]
fn old_test_llm_read_after_bufread_consume() {
    // Test that Read trait works correctly after consuming data via BufRead
    let data = b"Hello, World!";
    let mut reader = DynBufReader::new(Cursor::new(data));

    // Use BufRead to fill buffer
    let filled = reader.fill_buf().unwrap();
    assert_eq!(filled, b"Hello, World!");

    // Consume some bytes via BufRead
    reader.consume(7);

    // Read trait should return the unconsumed data
    let mut buf = [0u8; 6];
    let n = reader.read(&mut buf).unwrap();
    assert_eq!(n, 6);
    assert_eq!(&buf[..n], b"World!");
}

#[test]
fn old_test_llm_mixed_read_and_fill_buf() {
    let data = b"Hello, World! How are you?";
    let mut reader = DynBufReader::new(Cursor::new(data));

    // Use fill_buf
    let buf = reader.fill_buf().unwrap();
    assert_eq!(&buf[..5], b"Hello");

    // Consume
    reader.consume(7);

    // Use read
    let mut read_buf = [0u8; 6];
    let n = reader.read(&mut read_buf).unwrap();
    assert_eq!(n, 6);
    assert_eq!(&read_buf[..n], b"World!");

    // Use fill_buf again
    let buf = reader.fill_buf().unwrap();
    assert_eq!(&buf[..4], b" How");
}

#[test]
fn old_test_llm_read_line() {
    let data = b"Line 1\nLine 2\nLine 3";
    let mut reader = DynBufReader::new(Cursor::new(data));

    let mut line = String::new();
    let n = reader.read_line(&mut line).unwrap();
    assert_eq!(n, 7);
    assert_eq!(line, "Line 1\n");

    line.clear();
    let n = reader.read_line(&mut line).unwrap();
    assert_eq!(n, 7);
    assert_eq!(line, "Line 2\n");

    line.clear();
    let n = reader.read_line(&mut line).unwrap();
    assert_eq!(n, 6);
    assert_eq!(line, "Line 3");

    line.clear();
    let n = reader.read_line(&mut line).unwrap();
    assert_eq!(n, 0);
    assert_eq!(line, "");
}

#[test]
fn old_test_llm_read_until() {
    let data = b"key1:value1;key2:value2;";
    let mut reader = DynBufReader::new(Cursor::new(data));

    let mut buf = Vec::new();
    let n = reader.read_until(b':', &mut buf).unwrap();
    assert_eq!(n, 5);
    assert_eq!(&buf, b"key1:");

    buf.clear();
    let n = reader.read_until(b';', &mut buf).unwrap();
    assert_eq!(n, 7);
    assert_eq!(&buf, b"value1;");

    buf.clear();
    let n = reader.read_until(b':', &mut buf).unwrap();
    assert_eq!(n, 5);
    assert_eq!(&buf, b"key2:");
}

#[test]
fn old_test_llm_lines_iterator() {
    let data = b"First\nSecond\nThird\n";
    let reader = DynBufReader::new(Cursor::new(data));

    let lines: Vec<_> = reader.lines().collect::<Result<_, _>>().unwrap();
    assert_eq!(lines.len(), 3);
    assert_eq!(lines[0], "First");
    assert_eq!(lines[1], "Second");
    assert_eq!(lines[2], "Third");
}

#[test]
fn old_test_llm_split_iterator() {
    let data = b"a,b,c,d,e";
    let reader = DynBufReader::new(Cursor::new(data));

    let parts: Vec<_> = reader.split(b',').collect::<Result<_, _>>().unwrap();
    assert_eq!(parts.len(), 5);
    assert_eq!(parts[0], b"a");
    assert_eq!(parts[1], b"b");
    assert_eq!(parts[2], b"c");
    assert_eq!(parts[3], b"d");
    assert_eq!(parts[4], b"e");
}

#[test]
fn old_test_llm_read_exact() {
    let data = b"0123456789";
    let mut reader = DynBufReader::new(Cursor::new(data));

    let mut buf = [0u8; 5];
    reader.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"01234");

    reader.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"56789");

    // Should fail on EOF
    let result = reader.read_exact(&mut buf);
    assert!(result.is_err());
}

#[test]
fn old_test_llm_read_to_end() {
    let data = b"Hello, World!";
    let mut reader = DynBufReader::new(Cursor::new(data));

    let mut result = Vec::new();
    let n = reader.read_to_end(&mut result).unwrap();
    assert_eq!(n, 13);
    assert_eq!(result, b"Hello, World!");
}

#[test]
fn old_test_llm_read_to_string() {
    let data = b"Hello, World!";
    let mut reader = DynBufReader::new(Cursor::new(data));

    let mut result = String::new();
    let n = reader.read_to_string(&mut result).unwrap();
    assert_eq!(n, 13);
    assert_eq!(result, "Hello, World!");
}

#[test]
fn old_test_llm_large_lines() {
    // Test reading lines that are larger than CHUNK_SIZE
    let line = "x".repeat(CHUNK_SIZE * 2);
    let data = format!("{line}\n{line}\n");
    let mut reader = DynBufReader::new(Cursor::new(data.as_bytes()));

    let mut result = String::new();
    let n = reader.read_line(&mut result).unwrap();
    assert_eq!(n, CHUNK_SIZE * 2 + 1);
    assert_eq!(result.trim(), line);

    result.clear();
    let n = reader.read_line(&mut result).unwrap();
    assert_eq!(n, CHUNK_SIZE * 2 + 1);
    assert_eq!(result.trim(), line);
}

// ========== Edge cases ==========

#[test]
fn old_test_llm_alternating_read_operations() {
    let data = b"ABCDEFGHIJKLMNOP";
    let mut reader = DynBufReader::new(Cursor::new(data));

    // fill_buf
    let buf = reader.fill_buf().unwrap();
    assert_eq!(&buf[..2], b"AB");
    reader.consume(2);

    // read
    let mut read_buf = [0u8; 2];
    let n = reader.read(&mut read_buf).unwrap();
    assert_eq!(n, 2);
    assert_eq!(&read_buf, b"CD");

    // fill_buf
    let buf = reader.fill_buf().unwrap();
    assert_eq!(&buf[..2], b"EF");
    reader.consume(2);

    // read
    let n = reader.read(&mut read_buf).unwrap();
    assert_eq!(n, 2);
    assert_eq!(&read_buf, b"GH");
}

#[test]
fn old_test_llm_consume_and_compact() {
    let data = b"Hello, World! This is a test.";
    let mut reader = DynBufReader::new(Cursor::new(data));

    // Fill and consume
    let buf = reader.fill_buf().unwrap();
    assert_eq!(&buf[..5], b"Hello");
    reader.consume(7);

    // Manually compact
    reader.compact();

    // Continue reading
    let buf = reader.fill_buf().unwrap();
    assert_eq!(&buf[..5], b"World");
}

#[test]
fn old_test_llm_discard() {
    let data = b"Hello, World!";
    let mut reader = DynBufReader::new(Cursor::new(data));

    // Fill buffer
    let buf = reader.fill_buf().unwrap();
    assert_eq!(buf, b"Hello, World!");

    // Discard everything
    reader.discard();

    // Buffer should be empty but we're at EOF
    let buf = reader.fill_buf().unwrap();
    assert_eq!(buf, b"");
}

#[test]
fn old_test_llm_grow_shrink() {
    let data = vec![b'Z'; CHUNK_SIZE];
    let mut reader = DynBufReader::new(Cursor::new(data));

    let initial_cap = reader.buffer.cap();

    // Grow
    reader.grow();
    assert!(reader.buffer.cap() > initial_cap);

    // Shrink
    reader.shrink();
    assert_eq!(reader.buffer.cap(), CHUNK_SIZE);
}

#[test]
fn old_test_llm_utf8_boundary_handling() {
    // Test with multibyte UTF-8 characters
    let data = "Hello, 世界! 😀".as_bytes();
    let mut reader = DynBufReader::new(Cursor::new(data));

    let mut result = String::new();
    reader.read_to_string(&mut result).unwrap();
    assert_eq!(result, "Hello, 世界! 😀");
} */
*/
