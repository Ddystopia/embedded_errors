use core::ptr;

use crate::{ReportBuf, ReportContext};

pub struct ThreadLocalErrorBufs;

const PRIORITY_LEVELS: usize = 4;

struct Pair(u16, ReportBuf);
struct PriorityLocalBufs(core::cell::UnsafeCell<[Pair; PRIORITY_LEVELS]>);

static PRIORITY_LOCAL_BUFS: PriorityLocalBufs = PriorityLocalBufs(core::cell::UnsafeCell::new(
    [const { Pair(0, ReportBuf::new()) }; _],
));

unsafe impl Sync for PriorityLocalBufs {}

// not rtos-aware, only for interrupts (rtic etc)
#[inline(always)]
pub fn interrupt_priority_descriminator() -> u16 {
    let ipsr: u32;
    unsafe { core::arch::asm!("mrs {0}, ipsr", out(reg) ipsr) };
    (ipsr & 0x1FF) as u16 + 1
}

fn critical_section<F, R>(f: F) -> R
where
    F: FnOnce(&()) -> R,
{
    todo!()
}

// thread local for std
impl ReportContext for ThreadLocalErrorBufs {
    fn sync_error_buf() -> &'static ReportBuf {
        critical_section(|_| unsafe {
            let priority = interrupt_priority_descriminator();
            assert!(priority != 0, "reserved");
            let pairs = PRIORITY_LOCAL_BUFS.0.get().cast::<Pair>();
            for i in 0..PRIORITY_LEVELS {
                let pair = pairs.add(i);
                let (prio_p, buf_p) = (&raw mut (*pair).0, &raw const (*pair).1);
                let p = ptr::read(prio_p);
                if p == priority || p == 0 {
                    ptr::write(prio_p, priority);
                    return &*buf_p;
                }
            }
            panic!("Too many priority levels in use");
        })
    }
    async fn async_error_buf() -> &'static ReportBuf {
        Self::sync_error_buf()
    }
}
