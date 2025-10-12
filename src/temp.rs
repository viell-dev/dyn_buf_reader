//! This file contains old and generated code for my reference. That's it.

impl<R: ?Sized + Read> Read for DynBufReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let mut rem = self.fill_buf()?;
        let nread = rem.read(buf)?;
        self.consume(nread);
        Ok(nread)
    }
}

impl<R: ?Sized + Read> BufRead for DynBufReader<R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        self.buffer.fill_buffer()
    }

    fn consume(&mut self, amount: usize) {
        self.buffer.consume()
    }
}

impl<R: ?Sized + Read> DynBufRead for DynBufReader<R> {
    // TODO
}

// A buffered reader with a dynamically sized buffer that grows in 8KB chunks
// and allows peeking beyond the standard buffer size.
#[derive(Default)]
pub struct _DynBufReader<R: Read> {
    inner: R,
    buffer: Vec<u8>,
    pos: usize,             // Current read position in buffer
    filled: usize,          // Amount of valid data in buffer
    max_buffer_size: usize, // Maximum allowed buffer size (multiple of BUFFER_SIZE)
}

impl<R: Read> _DynBufReader<R> {
    // Creates a new `DynBufReader` with an initial 8KB buffer
    pub fn new(inner: R) -> Self {
        Self::with_max_size(inner, DEFAULT_MAX_SIZE)
    }

    // Creates a new `DynBufReader` with a custom maximum buffer size
    // The max_buffer_size will be rounded up to the nearest multiple of CHUNK_SIZE
    // and clamped to a reasonable maximum to prevent overflow.
    pub fn with_max_size(inner: R, max_buffer_size: usize) -> Self {
        Self {
            inner,
            buffer: vec![0; CHUNK_SIZE],
            pos: 0,
            filled: 0,
            max_buffer_size: Self::round_to_nearest_multiple(max_buffer_size),
        }
    }

    // Round a size up to the nearest chunk boundary, with overflow protection
    #[expect(clippy::arithmetic_side_effects, reason = "Bounds check makes it safe")]
    pub(crate) fn round_to_nearest_multiple(size: usize) -> usize {
        // Min and max checks
        if size <= CHUNK_SIZE {
            return CHUNK_SIZE;
        } else if size >= PRACTICAL_MAX_SIZE {
            return PRACTICAL_MAX_SIZE;
        }

        ((size + CHUNK_SIZE - 1) / CHUNK_SIZE) * CHUNK_SIZE
    }

    // Returns the maximum buffer size (always a multiple of CHUNK_SIZE)
    pub fn max_buffer_size(&self) -> usize {
        self.max_buffer_size
    }

    // Returns the current buffer size in bytes
    pub fn buffer_size(&self) -> usize {
        self.buffer.len()
    }

    // Returns the current buffer size in chunks (8KB units) - for tests
    pub(crate) fn buffer_chunks(&self) -> usize {
        self.buffer.len() / CHUNK_SIZE
    }

    // Returns the number of bytes available for reading without doing I/O
    pub fn available(&self) -> usize {
        self.filled - self.pos
    }

    // Ensures the buffer has at least `min_bytes` available for reading.
    // This may grow the buffer and/or read more data from the underlying reader.
    pub fn ensure_available(&mut self, min_bytes: usize) -> io::Result<usize> {
        // If we already have enough bytes, return early
        if self.available() >= min_bytes {
            return Ok(self.available());
        }

        // Calculate how much total buffer space we need
        let needed_total = self.pos + min_bytes;

        // Checks against maximum buffer size
        if needed_total > self.max_buffer_size {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "Token size {} exceeds maximum buffer size {}",
                    needed_total, self.max_buffer_size
                ),
            ));
        }

        // If we need more buffer space, grow it to the next multiple of CHUNK_SIZE
        if needed_total > self.buffer.len() {
            let needed_chunks = (needed_total + CHUNK_SIZE - 1) / CHUNK_SIZE;
            let new_size = needed_chunks * CHUNK_SIZE;
            self.buffer.resize(new_size, 0);
        }

        // Try to read more data to fulfill the request
        while self.available() < min_bytes {
            let bytes_read = self.inner.read(&mut self.buffer[self.filled..])?;
            // If we've hit EOF
            if bytes_read == 0 {
                break;
            }
            self.filled += bytes_read;
        }

        Ok(self.available())
    }

    // Peeks at up to `n` bytes without consuming them
    pub fn peek(&mut self, n: usize) -> io::Result<&[u8]> {
        self.ensure_available(n)?;
        let available = self.available().min(n);
        Ok(&self.buffer[self.pos..self.pos + available])
    }

    // Compacts the buffer by moving unconsumed data to the front and
    // shrinking the buffer to the smallest multiple of 8KB that fits the remaining data
    pub fn compact(&mut self) {
        // If there is nothing to compact
        if self.pos == 0 {
            return;
        }

        let remaining = self.available();

        if remaining == 0 {
            // No data remaining, reset to beginning
            self.pos = 0;
            self.filled = 0;
        } else {
            // Move remaining data to the front
            self.buffer.copy_within(self.pos..self.filled, 0);
            self.pos = 0;
            self.filled = remaining;
        }

        // Shrink buffer to the smallest multiple of CHUNK_SIZE that fits remaining data
        let min_chunks = if remaining == 0 {
            1
        } else {
            (remaining + CHUNK_SIZE - 1) / CHUNK_SIZE
        };
        let new_size = min_chunks * CHUNK_SIZE;

        if new_size < self.buffer.len() {
            self.buffer.resize(new_size, 0);
        }
    }

    // Consumes exactly `n` bytes from the buffer
    // Returns an error if there aren't enough bytes available
    pub fn consume_exact(&mut self, n: usize) -> io::Result<()> {
        if self.available() < n {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "Not enough bytes available to consume",
            ));
        }
        self.pos += n;
        Ok(())
    }

    // Peeks ahead while the predicate returns true, with an optional size limit.
    // Returns the matching slice, the number of bytes it spans, and whether it was truncated.
    pub fn peek_while_limited<F>(
        &mut self,
        mut predicate: F,
        max_bytes: Option<usize>,
    ) -> io::Result<(&[u8], usize, bool)>
    where
        F: FnMut(u8) -> bool,
    {
        let limit = max_bytes.unwrap_or(self.max_buffer_size);
        let mut checked = 0;

        loop {
            // Check if we've hit the limit
            if checked >= limit {
                return Ok((&self.buffer[self.pos..self.pos + checked], checked, true));
            }

            // Ensure we have at least one more byte than we've checked
            let available = self.ensure_available(checked + 1)?;

            // If we don't have any new bytes, we've hit EOF
            if available <= checked {
                break;
            }

            // Check the next byte
            let byte = self.buffer[self.pos + checked];
            if !predicate(byte) {
                break;
            }

            checked += 1;
        }

        Ok((&self.buffer[self.pos..self.pos + checked], checked, false))
    }

    // Peeks ahead while the predicate returns true, returning the slice that matches.
    // Uses the reader's maximum buffer size as the limit.
    pub fn peek_while<F>(&mut self, predicate: F) -> io::Result<(&[u8], usize)>
    where
        F: FnMut(u8) -> bool,
    {
        let (slice, len, truncated) = self.peek_while_limited(predicate, None)?;
        if truncated {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Token exceeded maximum size",
            ));
        }
        Ok((slice, len))
    }

    // Returns a reference to the underlying reader
    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    // Returns a mutable reference to the underlying reader
    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    // Unwraps this `DynBufReader`, returning the underlying reader
    pub fn into_inner(self) -> R {
        self.inner
    }
}

impl<R: Read> Read for _DynBufReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        // If we have data in our buffer, use it first
        if self.available() > 0 {
            let n = buf.len().min(self.available());
            buf[..n].copy_from_slice(&self.buffer[self.pos..self.pos + n]);
            self.pos += n;
            Ok(n)
        } else {
            // Buffer is empty, read directly from underlying reader
            self.inner.read(buf)
        }
    }
}

impl<R: Read> BufRead for _DynBufReader<R> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        // If we have no available data, try to read some
        if self.available() == 0 {
            // Reset position if we're at the end
            if self.pos == self.filled {
                self.pos = 0;
                self.filled = 0;
            }

            // Read more data
            let bytes_read = self.inner.read(&mut self.buffer[self.filled..])?;
            self.filled += bytes_read;
        }

        Ok(&self.buffer[self.pos..self.filled])
    }

    fn consume(&mut self, amt: usize) {
        self.pos = (self.pos + amt).min(self.filled);
    }
}

impl<R: Read> DynBufRead for _DynBufReader<R> {
    fn ensure_available(&mut self, min_bytes: usize) -> io::Result<usize> {
        self.ensure_available(min_bytes)
    }

    fn peek(&mut self, n: usize) -> io::Result<&[u8]> {
        self.peek(n)
    }

    fn available(&self) -> usize {
        self.available()
    }

    fn compact(&mut self) {
        self.compact()
    }
}

#[cfg(test)]
mod old_dev_tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn test_basic_reading() {
        let data = b"Hello, world!";
        let mut reader = _DynBufReader::new(Cursor::new(data));

        let mut buf = [0; 5];
        let n = reader.read(&mut buf).unwrap();
        assert_eq!(n, 5);
        assert_eq!(&buf, b"Hello");
    }

    #[test]
    fn test_peek() {
        let data = b"Hello, world!";
        let mut reader = _DynBufReader::new(Cursor::new(data));

        // Peek at first 5 bytes
        let peeked = reader.peek(5).unwrap();
        assert_eq!(peeked, b"Hello");

        // Data should still be available for reading
        let mut buf = [0; 5];
        let n = reader.read(&mut buf).unwrap();
        assert_eq!(n, 5);
        assert_eq!(&buf, b"Hello");
    }

    #[test]
    fn test_large_peek() {
        // Create data larger than default buffer
        let data = vec![b'A'; 16384]; // 16KB
        let mut reader = _DynBufReader::new(Cursor::new(data.clone()));

        // Peek at more than default buffer size
        let peeked = reader.peek(12000).unwrap();
        assert_eq!(peeked.len(), 12000);
        assert!(peeked.iter().all(|&b| b == b'A'));

        // Buffer should have grown
        assert!(reader.buffer_size() >= 16384);
    }

    #[test]
    fn test_compact() {
        let data = b"Hello, world! This is a test.";
        let mut reader = _DynBufReader::new(Cursor::new(data));

        // Read some data to fill buffer
        reader.ensure_available(20).unwrap();

        // Consume some bytes
        reader.consume_exact(7).unwrap(); // Consume "Hello, "

        let available_before = reader.available();
        let buffer_size_before = reader.buffer_size();

        // Compact the buffer
        reader.compact();

        // Data should be moved to front, buffer might be smaller
        assert_eq!(reader.pos, 0);
        assert_eq!(reader.available(), available_before);

        // Next read should get "world!"
        let mut buf = [0; 6];
        let n = reader.read(&mut buf).unwrap();
        assert_eq!(n, 6);
        assert_eq!(&buf, b"world!");
    }

    #[test]
    fn test_buffer_growth() {
        let data = vec![b'X'; 50000]; // 50KB
        let mut reader = _DynBufReader::new(Cursor::new(data));

        // Initially 1 chunk (8KB)
        assert_eq!(reader.buffer_chunks(), 1);

        // Request more than fits in current buffer
        reader.ensure_available(30000).unwrap();

        // Buffer should have grown to accommodate
        assert!(reader.buffer_chunks() >= 4); // At least 32KB
    }

    #[test]
    fn test_peek_while() {
        let data = b"hello123world";
        let mut reader = _DynBufReader::new(Cursor::new(data));

        // Peek while alphabetic
        let (matched, len) = reader.peek_while(|b| b.is_ascii_alphabetic()).unwrap();
        assert_eq!(matched, b"hello");
        assert_eq!(len, 5);

        // Consume what we matched
        reader.consume_exact(len).unwrap();

        // Now peek while numeric
        let (matched, len) = reader.peek_while(|b| b.is_ascii_digit()).unwrap();
        assert_eq!(matched, b"123");
        assert_eq!(len, 3);
    }

    #[test]
    fn test_max_size_rounding() {
        // Test that max size gets rounded up to chunk boundaries
        let data = b"test";
        let reader = _DynBufReader::with_max_size(Cursor::new(data), 10000); // 10KB

        // Should round up to 16KB (2 chunks)
        assert_eq!(reader.max_buffer_size(), 16384);

        let reader2 = _DynBufReader::with_max_size(Cursor::new(data), 8192); // Exact chunk
        assert_eq!(reader2.max_buffer_size(), 8192);

        let reader3 = _DynBufReader::with_max_size(Cursor::new(data), 1); // Tiny size
        assert_eq!(reader3.max_buffer_size(), 8192); // Rounds up to 1 chunk
    }

    #[test]
    fn test_overflow_protection() {
        let data = b"test";

        // Test with zero
        let reader = _DynBufReader::with_max_size(Cursor::new(data), 0);
        assert_eq!(reader.max_buffer_size(), CHUNK_SIZE);

        // Test with absurdly large value
        let reader2 = _DynBufReader::with_max_size(Cursor::new(data), usize::MAX);
        let max_chunks = usize::MAX / CHUNK_SIZE;
        let expected_max = max_chunks * CHUNK_SIZE;
        assert_eq!(reader2.max_buffer_size(), expected_max);

        // Test with value that would overflow during rounding
        let reader3 = _DynBufReader::with_max_size(Cursor::new(data), usize::MAX - 1000);
        assert_eq!(reader3.max_buffer_size(), expected_max);
    }

    #[test]
    fn test_large_peek_while() {
        // Test peek_while with data larger than initial buffer
        let mut data = vec![b'A'; 15000]; // 15KB of 'A's
        data.extend_from_slice(b"STOP");

        let mut reader = _DynBufReader::new(Cursor::new(data));

        let (matched, len) = reader.peek_while(|b| b == b'A').unwrap();
        assert_eq!(len, 15000);
        assert!(matched.iter().all(|&b| b == b'A'));

        // Buffer should have grown to accommodate
        assert!(reader.buffer_size() >= 15000);
    }

    #[test]
    fn test_sizes_at_or_below_chunk_size() {
        // All sizes <= CHUNK_SIZE should return CHUNK_SIZE
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(0),
            CHUNK_SIZE
        );
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(1),
            CHUNK_SIZE
        );
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(CHUNK_SIZE / 2),
            CHUNK_SIZE
        );
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(CHUNK_SIZE),
            CHUNK_SIZE
        );
    }

    #[test]
    fn test_sizes_at_or_above_max() {
        // All sizes >= PRACTICAL_MAX_SIZE should return PRACTICAL_MAX_SIZE
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(PRACTICAL_MAX_SIZE),
            PRACTICAL_MAX_SIZE
        );
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(usize::MAX),
            PRACTICAL_MAX_SIZE
        );
    }

    #[test]
    fn test_exact_multiples() {
        // Sizes that are exact multiples should stay the same (except for edge cases handled above)
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(2 * CHUNK_SIZE),
            2 * CHUNK_SIZE
        );
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(3 * CHUNK_SIZE),
            3 * CHUNK_SIZE
        );
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(10 * CHUNK_SIZE),
            10 * CHUNK_SIZE
        );
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(100 * CHUNK_SIZE),
            100 * CHUNK_SIZE
        );
    }

    #[test]
    fn test_rounding_up() {
        // Sizes that aren't exact multiples should round up
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(CHUNK_SIZE + 1),
            2 * CHUNK_SIZE
        );
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(
                CHUNK_SIZE + CHUNK_SIZE / 2
            ),
            2 * CHUNK_SIZE
        );
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(2 * CHUNK_SIZE - 1),
            2 * CHUNK_SIZE
        );

        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(2 * CHUNK_SIZE + 1),
            3 * CHUNK_SIZE
        );
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(3 * CHUNK_SIZE - 1),
            3 * CHUNK_SIZE
        );

        // Test with larger values
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(10 * CHUNK_SIZE + 1),
            11 * CHUNK_SIZE
        );
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(100 * CHUNK_SIZE + 1),
            101 * CHUNK_SIZE
        );
    }

    #[test]
    fn test_large_values_near_max() {
        // Test values close to but less than PRACTICAL_MAX_SIZE
        let near_max = PRACTICAL_MAX_SIZE - CHUNK_SIZE + 1;
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(near_max),
            PRACTICAL_MAX_SIZE
        );

        let second_largest = PRACTICAL_MAX_SIZE - CHUNK_SIZE;
        assert_eq!(
            _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(second_largest),
            PRACTICAL_MAX_SIZE - CHUNK_SIZE
        );
    }

    #[test]
    fn test_overflow_safety() {
        // These should not panic and should handle overflow gracefully
        let large_values = vec![
            usize::MAX,
            usize::MAX - 1,
            usize::MAX - CHUNK_SIZE,
            PRACTICAL_MAX_SIZE + 1,
        ];

        for value in large_values {
            let result = _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(value);
            // All should be capped at PRACTICAL_MAX_SIZE
            assert_eq!(result, PRACTICAL_MAX_SIZE);
            // And PRACTICAL_MAX_SIZE should be a multiple of CHUNK_SIZE
            assert_eq!(result % CHUNK_SIZE, 0);
        }
    }

    #[test]
    fn test_result_always_multiple_of_chunk_size() {
        // Property test: result should always be a multiple of CHUNK_SIZE
        let test_values = vec![
            0,
            1,
            100,
            1000,
            9999,
            CHUNK_SIZE - 1,
            CHUNK_SIZE,
            CHUNK_SIZE + 1,
            2 * CHUNK_SIZE - 1,
            2 * CHUNK_SIZE,
            2 * CHUNK_SIZE + 1,
            PRACTICAL_MAX_SIZE / 2,
            PRACTICAL_MAX_SIZE - 1,
            PRACTICAL_MAX_SIZE,
            usize::MAX,
        ];

        for value in test_values {
            let result = _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(value);
            assert_eq!(
                result % CHUNK_SIZE,
                0,
                "Result {} is not a multiple of CHUNK_SIZE for input {}",
                result,
                value
            );
            assert!(
                result >= CHUNK_SIZE,
                "Result {} is less than minimum CHUNK_SIZE for input {}",
                result,
                value
            );
            assert!(
                result <= PRACTICAL_MAX_SIZE,
                "Result {} exceeds PRACTICAL_MAX_SIZE for input {}",
                result,
                value
            );
        }
    }

    #[test]
    fn test_mathematical_correctness() {
        // For values in the normal range, verify the math is correct
        for i in 1..=10 {
            let exact_multiple = i * CHUNK_SIZE;
            let just_over = exact_multiple + 1;
            let just_under = exact_multiple - 1;

            // Skip the edge case where just_under would be <= CHUNK_SIZE
            if just_under > CHUNK_SIZE {
                assert_eq!(
                    _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(just_under),
                    exact_multiple
                );
            }

            assert_eq!(
                _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(exact_multiple),
                exact_multiple
            );
            assert_eq!(
                _DynBufReader::<Cursor<Vec<u8>>>::round_to_nearest_multiple(just_over),
                (i + 1) * CHUNK_SIZE
            );
        }
    }
}

pub fn compact(&mut self) {
    self.buf.copy_within(self.pos.., 0);
    self.len -= self.pos;
    self.pos = 0;

    let new_cap = Self::min_cap(self.len);
    self.buf.resize(new_cap, 0);
}

#[inline]
pub fn fill_buf(&mut self, mut reader: impl Read) -> io::Result<&[u8]> {
    // If we've reached the end of our internal buffer then we need to fetch some more data from
    // the reader. We're branching with `>=` instead of the more correct `==` to tell the
    // compiler that the `pos..filled` slice is always valid.
    if self.pos >= self.len {
        debug_assert!(self.pos == self.len);

        // Compact if the buffer grew beyond the default size
        if self.capacity() > 2 * CHUNK_SIZE {
            self.compact();
        }

        self.pos = 0;
        self.len = 0;

        let read_bytes = reader.read(&mut self.buf)?;

        self.len = read_bytes;
    }

    Ok(self.buffer())
}

/// Standard buffered read behavior - return existing data or fill once
pub fn fill_buf(&mut self, mut reader: impl Read) -> io::Result<&[u8]> {
    // If we have unconsumed data, return it
    if self.has_unconsumed_data() {
        return Ok(self.available_data());
    }

    // Compact if needed to make space
    if self.should_compact() {
        self.compact();
    }

    // Fill available space
    let available = self.buf.len() - self.filled;
    if available > 0 {
        let bytes_read = reader.read(&mut self.buf[self.filled..])?;
        self.filled += bytes_read;
    }

    Ok(self.available_data())
}

/// Enhanced version that can grow the buffer to read more data
pub fn fill_buf_with_growth(
    &mut self,
    mut reader: impl Read,
    min_available: Option<usize>,
) -> io::Result<&[u8]> {
    let min_size = min_available.unwrap_or(0);

    // If we have enough unconsumed data, return it
    if self.available_data().len() >= min_size {
        return Ok(self.available_data());
    }

    // Compact if fragmented
    if self.should_compact() {
        self.compact();
    }

    // Grow if we don't have enough space to meet min_size
    let available_space = self.buf.len() - self.filled;
    let current_data = self.available_data().len();

    if current_data + available_space < min_size {
        let needed_capacity = self.round_up_to_block(self.filled + (min_size - current_data));
        if needed_capacity > self.buf.len() {
            self.buf.resize(needed_capacity, 0);
        }
    }

    // Fill available space
    let available = self.buf.len() - self.filled;
    if available > 0 {
        let bytes_read = reader.read(&mut self.buf[self.filled..])?;
        self.filled += bytes_read;
    }

    Ok(self.available_data())
}

/// Peek ahead while predicate is true, growing buffer as needed
pub fn peek_while<F>(&mut self, mut reader: impl Read, mut predicate: F) -> io::Result<usize>
where
    F: FnMut(u8) -> bool,
{
    let mut index = 0;

    loop {
        let available = self.available_data();

        // Check if we have data at current index
        if index < available.len() {
            if predicate(available[index]) {
                index += 1;
                continue;
            } else {
                // Predicate failed, return how far we got
                return Ok(index);
            }
        }

        // Need more data - try to fill buffer
        let old_len = available.len();
        self.fill_buf_with_growth(&mut reader, Some(index + 1))?;

        // If we didn't get any new data, we've hit EOF
        if self.available_data().len() == old_len {
            return Ok(index);
        }
    }
}

/// Peek ahead for a specific byte sequence
pub fn peek_until(&mut self, mut reader: impl Read, delimiter: u8) -> io::Result<Option<usize>> {
    let pos = self.peek_while(&mut reader, |b| b != delimiter)?;

    // Check if we found the delimiter or hit EOF
    if pos < self.available_data().len() && self.available_data()[pos] == delimiter {
        Ok(Some(pos))
    } else {
        Ok(None) // EOF reached without finding delimiter
    }
}
