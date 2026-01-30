#![allow(async_fn_in_trait)]
#![cfg_attr(all(not(test), not(feature = "std")), no_std)]

// interesting idea: https://docs.rs/error-stack/latest/error_stack/

// todo: error stream merging

/*

Ways to access the buffer (no_std):
1. Pass &ReportBuf around
2. Pass a generic around -> &'static ReportBuf
3. Define a static with a map of (priority level) -> (&'static ReportBuf).
   Sounds the most ergonomic for me. It may even be dynamically initialized,
   so that we would remain portable. (`thread_local_bufs`)

*/

use core::{cell::RefCell, fmt};

mod format;
mod layout;
mod tagget_error_buf;

#[cfg(feature = "std")]
#[cfg(feature = "thread-local-errors")]
#[path = "std_thread_local_bufs.rs"]
pub mod thread_local_bufs;

// fixme: embedded thread local bufs are not finished
#[cfg(not(feature = "std"))]
#[cfg(feature = "thread-local-errors")]
#[cfg(target_arch = "arm")]
#[path = "cortex_thread_local_bufs.rs"]
pub mod thread_local_bufs;

#[cfg(feature = "unsafe-static-str-ranges")]
mod unsafe_static_str_ranges {
    #[allow(improper_ctypes)]
    unsafe extern "C" {
        #[link_name = "__data_start__"]
        static DATA_START: ();
        #[link_name = "__data_end__"]
        static DATA_END: ();
    }
    pub fn try_to_static(s: &str) -> Option<&'static str> {
        let p = s.as_ptr().cast::<()>();
        let start = &raw const DATA_START;
        let end = &raw const DATA_END;
        if (start <= p) && (p < end) {
            Some(unsafe { &*core::ptr::from_ref(s) })
        } else {
            None
        }
    }
}

use crate::format::Formatter;
use crate::layout::{ReportBufInner, Stream};
use crate::tagget_error_buf::TaggetErrorBufPtr;

// `Option` is when too manu errors are in use
pub struct LtReport<'a, E>(Option<TaggetErrorBufPtr<'a, E>>);
pub type Report<E> = LtReport<'static, E>;

#[derive(Debug, PartialEq, Eq)]
enum FrameEntry {
    Static(Stream, *const u8, usize),
    Offset(Stream, usize, usize),
    Merge(Stream, Stream),
    EndOfFrame(Stream),
}

#[repr(align(128))] // -> we can store 7 bits tag in the pointer
pub struct ReportBuf(RefCell<ReportBufInner>);
pub struct FrameBuilder<'a>(&'a mut ReportBufInner, Stream);

pub trait ReportContext {
    fn sync_error_buf() -> &'static ReportBuf;
    async fn async_error_buf() -> &'static ReportBuf;
}

pub trait Context {
    fn context(self, f: fmt::Arguments) -> Self;
    fn context_str(self, f: &'static str) -> Self;
    fn with_context<R: core::any::Any>(self, f: impl FnOnce(&mut FrameBuilder<'_>) -> R) -> Self;
}

pub trait ErrorExt: Sized + core::error::Error {
    const SIZE: usize = core::mem::size_of::<Self>();
    const _ASERT: () = const {
        if core::mem::size_of::<Self>() > 128 {
            panic!("Error type is too large to fit in the error buffer.");
        }
        if core::mem::align_of::<Self>() > 128 {
            panic!("Error type has too large alignment to fit in the error buffer.");
        }
    };

    async fn e_ctx_async<'a, C: ReportContext>(self) -> LtReport<'a, Self>
    where
        Self: 'a,
    {
        self.e(C::async_error_buf().await)
    }
    fn e_ctx<'a, C: ReportContext>(self) -> LtReport<'a, Self>
    where
        Self: 'a,
    {
        self.e(C::sync_error_buf())
    }
    fn e<'a>(self, ctx: &'a ReportBuf) -> LtReport<'a, Self> {
        _ = Self::_ASERT;
        LtReport(ctx.new_stream(self))
    }
}

impl<T: core::error::Error> ErrorExt for T {}

impl<'a, T, E> Context for Result<T, LtReport<'a, E>> {
    fn context(self, f: fmt::Arguments) -> Self {
        use core::fmt::Write;
        if let Err(LtReport(Some(ref token))) = self {
            let (buf, stream) = token.resplit();
            let mut buf = buf.borrow_mut();
            _ = FrameBuilder(&mut *buf, stream).write_fmt(f);
            buf.push_entry(FrameEntry::EndOfFrame(stream));
        }
        self
    }
    fn context_str(self, s: &'static str) -> Self {
        if let Err(LtReport(Some(ref token))) = self {
            let (buf, stream) = token.resplit();
            let mut buf = buf.borrow_mut();
            buf.push_entry(FrameEntry::from_static_str(stream, s));
            buf.push_entry(FrameEntry::EndOfFrame(stream));
        }
        self
    }
    fn with_context<R: core::any::Any>(self, f: impl FnOnce(&mut FrameBuilder<'_>) -> R) -> Self {
        if let Err(LtReport(Some(ref token))) = self {
            let (buf, stream) = token.resplit();
            let mut buf = buf.borrow_mut();
            f(&mut FrameBuilder(&mut *buf, stream));
            buf.push_entry(FrameEntry::EndOfFrame(stream));
        }
        self
    }
}

impl ReportBuf {
    pub const fn new() -> Self {
        Self(RefCell::new(ReportBufInner::new()))
    }
    fn borrow_mut(&self) -> core::cell::RefMut<'_, ReportBufInner> {
        self.0.borrow_mut()
    }
    #[cfg(test)]
    pub(crate) fn test_borrow_mut(&self) -> core::cell::RefMut<'_, ReportBufInner> {
        self.borrow_mut()
    }
    fn new_stream<'a, E>(&'a self, err: E) -> Option<TaggetErrorBufPtr<'a, E>> {
        let stream = self.0.borrow_mut().new_stream(err)?;
        Some(TaggetErrorBufPtr::new(self, stream))
    }
}

impl<'a, E> LtReport<'a, E> {
    pub fn into_inner(self) -> Option<E> {
        let mut taken = None;
        drop(self.map(|e| taken = Some(e)));
        taken
    }
    pub fn into<E2: From<E>>(self) -> LtReport<'a, E2> {
        self.map(|e| e.into())
    }
    pub fn from<E2: Into<E>>(e2: LtReport<'a, E2>) -> Self {
        e2.map(|e2| e2.into())
    }
    // Change the type of the error
    pub fn map<E2>(self, mapper: impl FnOnce(E) -> E2) -> LtReport<'a, E2> {
        if let Self(Some(token)) = self {
            LtReport(Some(tagget_error_buf::replace_error(token, mapper)))
        } else {
            LtReport(None)
        }
    }
    pub fn report(self) -> Option<Formatter<'a, E>> {
        Some(Formatter(self.0?))
    }
    // #[cfg(false)]
    pub fn merge<E2, ER>(
        mut self,
        other: LtReport<'a, E2>,
        merger: impl FnOnce(E, E2) -> ER,
    ) -> LtReport<'a, ER> {
        core::hint::black_box((&mut self, other, merger));
        // handle when from different buffers too
        todo!()
    }
    pub fn drop_many<const N: usize>(many: [Self; N]) {
        TaggetErrorBufPtr::drop_many(many.map(|e| e.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use FrameEntry::*;
    use std::fmt::Write;

    fn assert_frames_eq(fragments: &[FrameEntry], target_fragments: &[FrameEntry]) {
        let mut failures = Vec::new();
        for (i, (a, b)) in fragments.iter().zip(target_fragments).enumerate() {
            if match (a, b) {
                (Static(s1, _, l1), Static(s2, _, l2)) => s1 != s2 || l1 != l2,
                _ => a != b,
            } {
                failures.push((i, a, b));
            }
        }
        if !failures.is_empty() {
            panic!("Fragments do not match target: {failures:?}");
        }
        assert_eq!(fragments.len(), target_fragments.len());
    }

    #[test]
    fn reusing_the_buffer() {
        #[derive(Debug)]
        struct MyError;
        impl std::error::Error for MyError {}
        impl std::fmt::Display for MyError {
            fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                Ok(())
            }
        }

        let buf = ReportBuf::new();
        let e = Err::<(), _>(MyError.e(&buf))
            .with_context(|f| f.write_fmt(format_args!("{}", "x".repeat(700))).unwrap());
        assert_eq!(buf.test_borrow_mut().format_pos, 700);
        drop(e);
        assert_eq!(buf.test_borrow_mut().format_pos, 0);
        let e = Err::<(), _>(MyError.e(&buf))
            .with_context(|f| f.write_fmt(format_args!("{}", "x".repeat(600))).unwrap())
            .with_context(|f| f.write_fmt(format_args!("{}", "y".repeat(30))).unwrap());
        assert_eq!(buf.test_borrow_mut().format_pos, 630);
        drop(e);
        assert_eq!(buf.test_borrow_mut().format_pos, 0);
    }

    #[test]
    fn it_works() {
        #[derive(Debug)]
        struct MyError;

        impl std::error::Error for MyError {}
        impl std::fmt::Display for MyError {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "An error occurred.")
            }
        }

        let buf = ReportBuf::new();
        let e = foo(&buf, 13, 42).unwrap_err();
        let fragments = buf.test_borrow_mut().fragments().collect::<Vec<_>>();
        use FrameEntry::*;
        let target_fragments = [
            Static(Stream::ONE, core::ptr::null_mut(), 12),
            Offset(Stream::ONE, 0, 2),
            Static(Stream::ONE, core::ptr::null_mut(), 22),
            EndOfFrame(Stream::ONE),
            Static(Stream::ONE, core::ptr::null_mut(), 12),
            Offset(Stream::ONE, 2, 2),
            Static(Stream::ONE, core::ptr::null_mut(), 22),
            EndOfFrame(Stream::ONE),
        ];
        assert_frames_eq(&fragments, &target_fragments);

        let mut out = String::new();
        write!(&mut out, "{}", e.report().unwrap()).unwrap();
        assert_eq!(
            out,
            "\
Error: An error occurred.

Caused by:
  0: In `bar` at 42 we have seen an error
  1: In `foo` at 13 we have seen an error
"
        );

        #[inline(never)]
        fn foo(buf: &ReportBuf, x: usize, y: usize) -> Result<(), LtReport<'_, MyError>> {
            // https://internals.rust-lang.org/t/fmt-arguments-expose-pieces-maybe-add-write-static-str-to-write/23479
            // bar(buf, y).context(format_args!("In `foo` at {x} we have seen an error"))?;

            bar(buf, y).with_context(|f| {
                write!(f, "In `foo` at ")?;
                write!(f, "{}", x)?;
                write!(f, " we have seen an error")
            })?;

            Ok(())
        }

        #[inline(never)]
        fn bar(buf: &ReportBuf, y: usize) -> Result<(), LtReport<'_, MyError>> {
            let err = || Err(MyError.e(&buf));

            err().with_context(|f| {
                // write!(f, "In `bar` at {y} we have seen an error")
                write!(f, "In `bar` at ")?;
                write!(f, "{}", y)?;
                write!(f, " we have seen an error")
            })?;

            Ok(())
        }
    }

    #[test]
    fn simple_multi_level() {
        #[derive(Debug)]
        struct MyError;

        impl std::error::Error for MyError {}
        impl std::fmt::Display for MyError {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "An error occurred.")
            }
        }

        let buf = ReportBuf::new();
        let e = foo(&buf, 13, 42, 69).unwrap_err();

        let mut out = String::new();
        write!(&mut out, "{}", e.report().unwrap()).unwrap();
        assert_eq!(
            out,
            "\
Error: An error occurred.

Caused by:
  0: In `quix` at 69 we have seen an error
  1: In `baz` we have seen some error
  2: In `bar` at 42 we have seen an error
  3: In `foo` at 13 we have seen an error
"
        );

        #[inline(never)]
        fn foo(buf: &ReportBuf, x: usize, y: usize, z: usize) -> Result<(), LtReport<'_, MyError>> {
            bar(buf, y, z).context(format_args!("In `foo` at {x} we have seen an error"))?;

            Ok(())
        }

        #[inline(never)]
        fn bar(buf: &ReportBuf, y: usize, z: usize) -> Result<(), LtReport<'_, MyError>> {
            baz(buf, z).context(format_args!("In `bar` at {y} we have seen an error"))?;

            Ok(())
        }

        #[inline(never)]
        fn baz(buf: &ReportBuf, z: usize) -> Result<(), LtReport<'_, MyError>> {
            quix(buf, z).context_str("In `baz` we have seen some error")?;

            Ok(())
        }

        #[inline(never)]
        fn quix(buf: &ReportBuf, z: usize) -> Result<(), LtReport<'_, MyError>> {
            let err = || Err(MyError.e(&buf));

            err().context(format_args!("In `quix` at {z} we have seen an error"))?;

            Ok(())
        }
    }

    #[test]
    fn sensetive_error() {
        #[derive(Debug)]
        struct MyError(String);

        impl std::error::Error for MyError {}
        impl std::fmt::Display for MyError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(&self.0)
            }
        }

        let buf = ReportBuf::new();
        let e = |i: usize| {
            Err::<(), _>(MyError(format!("Hello, World [{i}]!")).e(&buf))
                .context(format_args!("Creating error number {i}"))
                .unwrap_err()
        };

        // beware: only 8 errors can be stored at once
        let e1 = e(1);
        let e2 = e(2);
        let e3 = e(3);
        let e4 = e(4);
        let e5 = e(5);
        drop(e3);
        let e6 = e(6);
        let e7 = e(7);
        let e8 = e(8);
        drop(e6);
        drop(e4);
        let e9 = e(9);

        LtReport::drop_many([e1, e2, e8]);

        let mut out5 = String::new();
        let mut out7 = String::new();
        let mut out9 = String::new();

        write!(&mut out5, "{}", e5.report().unwrap()).unwrap();
        write!(&mut out7, "{}", e7.report().unwrap()).unwrap();
        write!(&mut out9, "{}", e9.report().unwrap()).unwrap();

        assert_eq!(
            out5,
            "Error: Hello, World [5]!\n\nCaused by:\n  0: Creating error number 5\n"
        );
        assert_eq!(
            out7,
            "Error: Hello, World [7]!\n\nCaused by:\n  0: Creating error number 7\n"
        );
        assert_eq!(
            out9,
            "Error: Hello, World [9]!\n\nCaused by:\n  0: Creating error number 9\n"
        );
    }

    #[test]
    fn merge_consequtive_offsets() {
        #[derive(Debug)]
        struct MyError;

        impl std::error::Error for MyError {}
        impl std::fmt::Display for MyError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("Hi")
            }
        }

        #[inline(never)]
        fn mystery() -> i32 {
            42
        }

        let buf = ReportBuf::new();
        let e = Err::<(), _>(MyError.e(&buf))
            .with_context(|f| {
                write!(f, "x")?;
                write!(f, "{}", mystery())?;
                write!(f, "{}", mystery())?;
                write!(f, "{}", mystery())?;
                write!(f, "y")
            })
            .unwrap_err();

        let target_fragments = [
            FrameEntry::Static(Stream::ONE, core::ptr::null(), 1),
            FrameEntry::Offset(Stream::ONE, 0, 6),
            FrameEntry::Static(Stream::ONE, core::ptr::null(), 1),
            FrameEntry::EndOfFrame(Stream::ONE),
        ];
        let fragments = buf.test_borrow_mut().fragments().collect::<Vec<_>>();
        assert_frames_eq(&fragments, &target_fragments);

        let mut out = String::new();
        write!(&mut out, "{}", e.report().unwrap()).unwrap();
        assert_eq!(out, "Error: Hi\n\nCaused by:\n  0: x424242y\n");
    }

    #[ignore] // merging is not implemented yet
    #[test]
    fn merge() {
        #[derive(Debug)]
        struct E(E1, E2);
        #[derive(Debug)]
        struct E1;
        #[derive(Debug)]
        struct E2;

        impl std::error::Error for E {}
        impl std::error::Error for E1 {}
        impl std::error::Error for E2 {}

        impl std::fmt::Display for E {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "E[{}{}]", self.0, self.1)
            }
        }
        impl std::fmt::Display for E1 {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "E1.")
            }
        }
        impl std::fmt::Display for E2 {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "E2.")
            }
        }

        let buf = ReportBuf::new();

        let e1 = E1.e(&buf);
        let e2 = E2.e(&buf);

        let e = e1.merge(e2, |e1, e2| E(e1, e2));

        panic!("{}", e.report().unwrap());
    }
}
