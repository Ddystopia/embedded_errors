use core::marker::PhantomData;

use crate::{ReportBuf, layout::Stream};

// Invariant: `E` is stored at `Stream` where the tag points
// Invariant: tag is a valid `Stream`
// todo: NonNull 
pub(crate) struct TaggetErrorBufPtr<'a, E>(PhantomData<(&'a E, &'a ReportBuf)>, *const ReportBuf);

pub(crate) fn replace_error<'a, E1, E2>(
    tag: TaggetErrorBufPtr<'a, E1>,
    mapper: impl FnOnce(E1) -> E2,
) -> TaggetErrorBufPtr<'a, E2> {
    // Whanever happens inside `mapper`, we are holding tag for that error
    // thus no one will touch that stream, thus we can read/write it safely
    // Even if `mapper` panics, we "leaked" the error my splitting and given
    // ownership to the caller.

    let (buf, stream) = tag.split();
    let e1 = {
        let mut buf = buf.borrow_mut();
        let place = buf.place_of_stream_mut(stream);
        // Safety: Invariant
        unsafe { core::ptr::read(place) }
    };
    let e2 = mapper(e1);
    {
        let mut buf = buf.borrow_mut();
        let place = buf.place_of_stream_mut::<E2>(stream);
        // Safety: `place` is valid for writes
        unsafe { core::ptr::write(place, e2) };
    }

    TaggetErrorBufPtr::new(buf, stream)
}

impl<E> Drop for TaggetErrorBufPtr<'_, E> {
    fn drop(&mut self) {
        let (buf, stream) = self.resplit();
        let streams = [Some(stream)];
        // Safety: Invariant
        unsafe { buf.borrow_mut().remove_errors::<E>(&streams) }
    }
}

impl<'a, E> TaggetErrorBufPtr<'a, E> {
    pub fn new(buf: &'a ReportBuf, stream: Stream) -> Self {
        let stream = stream.as_usize() & 0x7F;
        let ptr = core::ptr::from_ref(buf).map_addr(|p| p | stream);
        Self(PhantomData, ptr)
    }
    pub fn drop_many<const N: usize>(many: [Option<Self>; N]) {
        if let Some(buf) = many.iter().find_map(Option::as_ref) {
            let buf = buf.buf();
            let streams = many.map(|e| e.map(|e| e.split().1));
            // Safety: Invariant
            unsafe { buf.borrow_mut().remove_errors::<E>(&streams) }
        }
    }
    fn split_inner(&self) -> (&'a ReportBuf, Stream) {
        let stream = self.1.addr() as u8 & 0x7F;
        let buf = self.1.map_addr(|p| p & !0x7F);
        // Safety: Invariant
        unsafe { (&*buf, Stream::new_uncheked(stream)) }
    }
    pub fn get_error(&self, buf: &crate::layout::ReportBufInner) -> &E {
        let place = buf.place_of_stream(self.split_inner().1);
        // Safety: Invariant
        unsafe { &*place }
    }
    pub fn buf(&self) -> &'a ReportBuf {
        self.split_inner().0
    }
    pub fn resplit(&self) -> (&ReportBuf, Stream) {
        self.split_inner()
    }
    pub fn split(self) -> (&'a ReportBuf, Stream) {
        let this = core::mem::ManuallyDrop::new(self);
        this.split_inner()
    }
}
