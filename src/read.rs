use std::io::BufRead;

pub trait DynBufRead: BufRead {
    fn grow(&mut self);
    fn shrink(&mut self);
    fn discard(&mut self);
    fn compact(&mut self);
}
