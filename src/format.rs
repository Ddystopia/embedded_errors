use core::fmt;

use crate::tagget_error_buf::TaggetErrorBufPtr;

pub struct Formatter<'a, E>(pub(crate) TaggetErrorBufPtr<'a, E>);

impl<E: core::error::Error> fmt::Display for Formatter<'_, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (buf, stream) = self.0.resplit();
        let buf = buf.borrow_mut();
        let format_buf = &buf.format_buffer.inner[..];
        let err = self.0.get_error(&*buf);
        writeln!(f, "Error: {err}")?;

        let mut i = 0;
        let mut fragments = buf.fragments().filter(|f| f.stream() == stream);
        let mut next = fragments.next();

        if next.is_some() {
            writeln!(f, "\nCaused by:")?;
        }

        'all: while let Some(ref mut frame) = next {
            if frame.is_end_of_frame() {
                writeln!(f, "{i}: <empty frame>")?;
                i += 1;
                next = fragments.next();
                continue;
            }

            write!(f, "  {i}: ")?;

            'frame: loop {
                // SAFETY: both `frame` and `format_buf` are from the same `ErrorBuf`
                //         thus `frame` always contains valid `&'static str`.
                f.write_str(unsafe { frame.resolve(format_buf) })?;

                match fragments.next() {
                    Some(f) => *frame = f,
                    None => {
                        writeln!(f)?;
                        break 'all;
                    }
                };
                if frame.is_end_of_frame() {
                    writeln!(f)?;
                    next = fragments.next();
                    i += 1;
                    break 'frame;
                }
            }
        }

        Ok(())
    }
}
