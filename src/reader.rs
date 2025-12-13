use crate::DynBufRead;
use crate::buffer::Buffer;
use crate::constants::DEFAULT_MAX_SIZE;
use std::io::{self, BufRead, Read};

pub struct DynBufReader<R: ?Sized> {
    buffer: Buffer,
    max_capacity: usize,
    reader: R,
}

impl<R: Read> DynBufReader<R> {
    pub fn new(reader: R) -> DynBufReader<R> {
        DynBufReader::with_max_capacity(DEFAULT_MAX_SIZE, reader)
    }

    pub fn with_max_capacity(max_capacity: usize, reader: R) -> DynBufReader<R> {
        DynBufReader {
            buffer: Buffer::new(),
            max_capacity: Buffer::cap_up(max_capacity),
            reader,
        }
    }
}

impl<R: ?Sized> DynBufReader<R> {
    // TODO: stuff

    pub fn grow(&mut self) {
        if self.buffer.cap() < self.max_capacity {
            self.buffer.grow();
        }
    }

    pub fn shrink(&mut self) {
        self.buffer.shrink();
    }

    pub fn consume(&mut self, amt: usize) {
        self.buffer.consume(amt);
    }

    pub fn discard(&mut self) {
        self.buffer.discard();
    }

    pub fn compact(&mut self) {
        self.buffer.compact();
    }
}

impl<R: Read + ?Sized> DynBufReader<R> {
    // TODO: Peek stuff.
}

impl<R: Read + ?Sized> Read for DynBufReader<R> {
    #[expect(clippy::indexing_slicing, reason = "Buffer invariant makes it safe")]
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if self.buffer.pos() >= self.buffer.len() {
            debug_assert!(self.buffer.pos() == self.buffer.len());
            // We've consumed all the data we have

            // Cap the fill amount to respect max_capacity
            let max_allowed = self.max_capacity.saturating_sub(self.buffer.len());
            let capped_amt = buf.len().min(max_allowed);

            // Read at least the requested amount of data (up to max_capacity)
            let _ = self.buffer.fill_amount(&mut self.reader, capped_amt)?;
        }

        // Get the range of data to give
        let start = self.buffer.pos();
        let end = self
            .buffer
            .pos()
            .saturating_add(buf.len())
            .min(self.buffer.len());

        // Get the slice of the data
        let data = &self.buffer.buf()[start..end];

        // Get count of read bytes
        let bytes_read = data.len();

        // Copy the data into the target buffer
        buf[..bytes_read].copy_from_slice(data);

        // Mark the now read bytes as consumed
        self.consume(bytes_read);

        // Return the number of read bytes
        Ok(bytes_read)
    }
}

impl<R: Read + ?Sized> BufRead for DynBufReader<R> {
    #[expect(clippy::indexing_slicing, reason = "Buffer invariant makes it safe")]
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        if self.buffer.pos() >= self.buffer.len() {
            debug_assert!(self.buffer.pos() == self.buffer.len());
            // We've consumed all the data we have

            if self.buffer.len() >= self.buffer.cap() {
                debug_assert!(self.buffer.len() == self.buffer.cap());
                // The buffer is full

                // Try to grow the buffer
                self.grow();
            }

            // Read to fill the internal buffer
            let _ = self.buffer.fill(&mut self.reader)?;
        }

        // Return buffered data
        Ok(&self.buffer.buf()[self.buffer.pos()..])
    }

    fn consume(&mut self, amt: usize) {
        self.consume(amt);
    }
}

impl<R: Read + ?Sized> DynBufRead for DynBufReader<R> {
    // TODO: more stuff...
    fn grow(&mut self) {
        self.grow();
    }
    fn shrink(&mut self) {
        self.shrink();
    }
    fn discard(&mut self) {
        self.discard();
    }
    fn compact(&mut self) {
        self.compact();
    }
}

#[cfg(test)]
#[expect(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    reason = "Okay in tests"
)]
mod tests {
    use super::*;

    mod impl_read {
        use crate::constants::CHUNK_SIZE;

        use super::*;
        use std::io::{Cursor, Read};

        #[test]
        fn test_read() {
            let data = "Hello, World!";
            let cur = Cursor::new(data);
            let mut reader = DynBufReader::new(cur);
            let mut buf = [0u8; 20];

            let len = reader.read(&mut buf).unwrap();

            assert_eq!(len, 13);
            assert_eq!(&buf[..len], data.as_bytes());
        }

        #[test]
        fn test_read_multiple_times() {
            let data = "Hello, World!";
            let cur = Cursor::new(data);
            let mut reader = DynBufReader::new(cur);
            let mut buf = [0u8; 5];

            // First read
            let len = reader.read(&mut buf).unwrap();

            assert_eq!(len, 5);
            assert_eq!(&buf[..len], b"Hello");

            // Second read
            let len = reader.read(&mut buf).unwrap();

            assert_eq!(len, 5);
            assert_eq!(&buf[..len], b", Wor");

            // Third read
            let len = reader.read(&mut buf).unwrap();

            assert_eq!(len, 3);
            assert_eq!(&buf[..len], b"ld!");

            // EOF
            let len = reader.read(&mut buf).unwrap();

            assert_eq!(len, 0);
            assert_eq!(&buf[..len], b"");
        }

        #[test]
        fn test_read_empty() {
            let data = "";
            let cur = Cursor::new(data);
            let mut reader = DynBufReader::new(cur);
            let mut buf = [0u8; 5];

            let len = reader.read(&mut buf).unwrap();

            assert_eq!(len, 0);
        }

        #[test]
        fn test_read_respects_max_capacity() {
            let data = "x".repeat(CHUNK_SIZE * 2);
            let cur = Cursor::new(data.as_str());
            let mut reader = DynBufReader::with_max_capacity(CHUNK_SIZE, cur);
            let mut buf = vec![0u8; CHUNK_SIZE * 3];

            // First read should cap at max_capacity, which we set to CHUNK_SIZE
            let len1 = reader.read(&mut buf).unwrap();

            assert!(len1 > 0);
            assert!(len1 <= CHUNK_SIZE, "Read should not exceed max_capacity");

            // Buffer is now full, we need to compact to read more
            let len_blocked = reader.read(&mut buf).unwrap();

            assert_eq!(
                len_blocked, 0,
                "Should not be able to read more than max_capacity"
            );

            // Use compact to clear the consumed data
            reader.compact();

            // Read more data, this should be the rest of it
            let len2 = reader.read(&mut buf).unwrap();

            assert!(len2 > 0);
            assert!(len2 <= CHUNK_SIZE, "Read should not exceed max_capacity");

            // Verify buffer capacity didn't grow
            assert_eq!(
                reader.buffer.cap(),
                CHUNK_SIZE,
                "Buffer shouldn't grow above max_capacity"
            );

            // Verify we've read all data, as expected
            let total = len1 + len2;

            assert_eq!(data.len(), total);
        }
    }

    mod impl_bufread {
        use std::io::Cursor;

        use super::*;

        #[test]
        fn test_fill_buf() {
            let data = "Hello, World!";
            let cur = Cursor::new(data);
            let mut reader = DynBufReader::new(cur);

            // Compare filled data matches
            let filled = reader.fill_buf().unwrap();

            assert_eq!(filled, data.as_bytes());
        }

        #[test]
        fn test_fill_buf_multiple_times() {
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
        fn test_fill_buf_empty() {
            let data = "";
            let cur = Cursor::new(data);
            let mut reader = DynBufReader::new(cur);

            let filled = reader.fill_buf().unwrap();

            assert_eq!(filled, data.as_bytes());
        }
    }

    // TODO: Add useful tests and not just LLM vomit.

    // Claude generated tests below: -------------------------------------------
    /*

    #[test]
    fn test_llm_fill_buf_empty() {
        let data = b"";
        let mut reader = DynBufReader::new(Cursor::new(data));

        let buf = reader.fill_buf().unwrap();
        assert_eq!(buf, b"");
    }

    #[test]
    fn test_llm_fill_buf_grows_when_full() {
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
    fn test_llm_fill_buf_with_consume_cycle() {
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
    fn test_llm_fill_buf_consume_zero() {
        let data = b"Hello";
        let mut reader = DynBufReader::new(Cursor::new(data));

        let buf = reader.fill_buf().unwrap();
        assert_eq!(buf, b"Hello");

        reader.consume(0);

        let buf = reader.fill_buf().unwrap();
        assert_eq!(buf, b"Hello");
    }

    #[test]
    fn test_llm_fill_buf_consume_beyond_available() {
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
    fn test_llm_fill_buf_eof_after_consume() {
        // Test that fill_buf correctly returns empty slice at EOF
        let data = b"Hello, World!";
        let mut reader = DynBufReader::new(Cursor::new(data));

        // Fill buffer
        let buf = reader.fill_buf().unwrap();
        assert_eq!(buf, b"Hello, World!");

        // Consume all data
        reader.consume(13);

        // fill_buf should attempt to refill but return empty (EOF reached)
        let buf = reader.fill_buf().unwrap();
        assert_eq!(buf, b"", "Should return empty slice at EOF");
    }

    #[test]
    fn test_llm_fill_buf_respects_max_capacity() {
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
    fn test_llm_read_after_bufread_consume() {
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
    fn test_llm_mixed_read_and_fill_buf() {
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
    fn test_llm_read_line() {
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
    fn test_llm_read_until() {
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
    fn test_llm_lines_iterator() {
        let data = b"First\nSecond\nThird\n";
        let reader = DynBufReader::new(Cursor::new(data));

        let lines: Vec<_> = reader.lines().collect::<Result<_, _>>().unwrap();
        assert_eq!(lines.len(), 3);
        assert_eq!(lines[0], "First");
        assert_eq!(lines[1], "Second");
        assert_eq!(lines[2], "Third");
    }

    #[test]
    fn test_llm_split_iterator() {
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
    fn test_llm_read_exact() {
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
    fn test_llm_read_to_end() {
        let data = b"Hello, World!";
        let mut reader = DynBufReader::new(Cursor::new(data));

        let mut result = Vec::new();
        let n = reader.read_to_end(&mut result).unwrap();
        assert_eq!(n, 13);
        assert_eq!(result, b"Hello, World!");
    }

    #[test]
    fn test_llm_read_to_string() {
        let data = b"Hello, World!";
        let mut reader = DynBufReader::new(Cursor::new(data));

        let mut result = String::new();
        let n = reader.read_to_string(&mut result).unwrap();
        assert_eq!(n, 13);
        assert_eq!(result, "Hello, World!");
    }

    #[test]
    fn test_llm_large_lines() {
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
    fn test_llm_alternating_read_operations() {
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
    fn test_llm_consume_and_compact() {
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
    fn test_llm_discard() {
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
    fn test_llm_grow_shrink() {
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
    fn test_llm_utf8_boundary_handling() {
        // Test with multibyte UTF-8 characters
        let data = "Hello, 世界! 😀".as_bytes();
        let mut reader = DynBufReader::new(Cursor::new(data));

        let mut result = String::new();
        reader.read_to_string(&mut result).unwrap();
        assert_eq!(result, "Hello, 世界! 😀");
    } */
}
