use crate::{ReportBuf, ReportContext};

pub struct ThreadLocalErrorBufs;

impl ReportContext for ThreadLocalErrorBufs {
    fn sync_error_buf() -> &'static ReportBuf {
        thread_local! {
            static BUF: &'static ReportBuf = Box::leak(Box::new(ReportBuf::new()));
        }
        BUF.with(|b| *b)
    }
    async fn async_error_buf() -> &'static ReportBuf {
        Self::sync_error_buf()
    }
}
