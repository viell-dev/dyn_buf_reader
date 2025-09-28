mod buffer;

use crate::DynBufRead;
use crate::constants::{CHUNK_SIZE, DEFAULT_MAX_SIZE, PRACTICAL_MAX_SIZE};
use buffer::Buffer;
use std::io::{self, BufRead, Read};

pub struct DynBufReader<R: ?Sized> {
    buffer: Buffer,
    inner: R,
}

impl<R: Read> DynBufReader<R> {
    // TODO: everything
}

#[cfg(test)]
mod tests {
    use super::*;
}
