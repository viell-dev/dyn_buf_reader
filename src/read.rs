use std::io::{self, Read};

/// A `DynBufRead` is an alternative to `BufRead` with a buffer that can grow and shrink in size as
/// needed. This allows for peeking far into this source without by growing the buffer as needed.
/// Shrinking requires a manual call to [`compact()`].
///
/// TODO: More docs
///
/// [`compact()`]: DynBufRead::compact
pub trait DynBufRead: Read {}
