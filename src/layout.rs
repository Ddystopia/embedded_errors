use super::*;
use const_generic_alignment::Aligned;
use core::{
    convert::identity,
    fmt::{self, Write},
    num::NonZero,
    ptr::{self, without_provenance},
};

const ALIGN: usize = ERROR_SIZE;
const ERROR_COUNT: usize = 8;
const ERROR_SIZE: usize = 32;
const CONTEXT_ENTRIES: usize = 50;
const FORMAT_BUFFER_SIZE: usize = 768;
type UsedErrorsMask = u32;

const _: () = assert!(UsedErrorsMask::BITS as usize >= ERROR_COUNT + 1);

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub(crate) struct Stream(NonZero<u8>);

pub(crate) struct ReportBufInner {
    pub boxed_error: [Aligned<[u8; ERROR_SIZE], ALIGN>; ERROR_COUNT],
    pub used_errors_mask: UsedErrorsMask,
    pub format_buffer: Aligned<[u8; FORMAT_BUFFER_SIZE], 64>,
    pub format_pos: usize,
    pub bases: [*const u8; CONTEXT_ENTRIES],
    pub lens: [u16; CONTEXT_ENTRIES],
    pub streams: [Option<Stream>; CONTEXT_ENTRIES],
    pub entries: usize,
}

impl Stream {
    #[cfg(test)]
    pub const ONE: Self = Stream(NonZero::<u8>::MIN);

    #[inline(always)]
    pub fn new(value: u8) -> Option<Self> {
        Some(Self(NonZero::new(value)?))
    }
    #[inline(always)]
    pub unsafe fn new_uncheked(value: u8) -> Self {
        unsafe { Self(NonZero::new_unchecked(value)) }
    }
    #[inline(always)]
    pub fn mask(self) -> UsedErrorsMask {
        1 << self.0.get() as UsedErrorsMask
    }
    #[inline(always)]
    pub fn as_usize(self) -> usize {
        self.0.get() as usize
    }
}

impl ReportBufInner {
    pub const fn new() -> Self {
        Self {
            boxed_error: [const { Aligned::new([0; _]) }; _],
            format_buffer: Aligned::new([0; _]),
            format_pos: 0,
            bases: [ptr::null(); _],
            lens: [0; _],
            streams: [None; _],
            entries: 0,
            used_errors_mask: 0,
        }
    }
    #[inline(always)]
    pub fn get_entry(s: Stream, b: *const u8, l: u16) -> FrameEntry {
        if l == FrameEntry::EOF {
            FrameEntry::EndOfFrame(s)
        } else if l == FrameEntry::MERGE {
            FrameEntry::Merge(s, Stream::new(b as usize as u8).unwrap())
        } else if l & FrameEntry::RANGE != 0 {
            FrameEntry::Offset(s, b as usize, (l & !FrameEntry::RANGE) as usize)
        } else {
            FrameEntry::Static(s, b, l as usize)
        }
    }
    pub fn fragments(&self) -> impl Iterator<Item = FrameEntry> + '_ {
        self.bases
            .iter()
            .zip(&self.lens)
            .zip(self.streams.iter().map(|s| s.expect("Must be initialized")))
            .map(|((&b, &l), s)| Self::get_entry(s, b, l))
            .take(self.entries)
    }
    #[inline(always)]
    pub fn null(&mut self, range: core::ops::Range<usize>) {
        self.bases[range.clone()].fill(ptr::null());
        self.lens[range.clone()].fill(0);
        self.streams[range].fill(None);
    }
    pub fn push_entry(&mut self, entry: FrameEntry) {
        use FrameEntry::*;
        let cap = |l: usize| l.min(FrameEntry::MAX_LEN as usize) as u16;
        let (s, b, l) = match entry {
            Static(s, b, l) => (s, b, cap(l)),
            Offset(s, b, l) => {
                let v = (s, without_provenance(b), cap(l) | FrameEntry::RANGE);
                if self.merge_offset(self.entries, v.0, v.1, v.2).is_some() {
                    return;
                }
                v
            }
            Merge(s, s2) => (s, without_provenance(s2.as_usize()), FrameEntry::MERGE),
            EndOfFrame(s) => (s, ptr::null(), FrameEntry::EOF),
        };
        self.bases[self.entries] = b;
        self.lens[self.entries] = l;
        self.streams[self.entries] = Some(s);
        self.entries += 1;
    }
    const fn assert_error<E>() {
        assert!(size_of::<E>() <= ERROR_SIZE, "Error is too large");
        assert!(align_of::<E>() <= ALIGN, "Error's alignment is too large");
        assert!(UsedErrorsMask::BITS <= u8::MAX as u32,);
    }
    #[inline(always)]
    pub fn place_of_stream<E>(&self, stream: Stream) -> *const E {
        const { Self::assert_error::<E>() };
        self.boxed_error[stream.0.get() as usize - 1]
            .inner
            .as_ptr()
            .cast::<E>()
    }
    // Returning value is valid for reads and writes of `E`, properly aligned.
    #[inline(always)]
    pub fn place_of_stream_mut<E>(&mut self, stream: Stream) -> *mut E {
        const { Self::assert_error::<E>() };
        self.boxed_error[stream.0.get() as usize - 1]
            .inner
            .as_mut_ptr()
            .cast::<E>()
    }
    pub fn is_full(&self) -> bool {
        let stream = (self.used_errors_mask | 1).trailing_ones() as UsedErrorsMask;
        stream as usize - 1 == ERROR_COUNT
    }
    // stream 0 is reserved
    pub fn new_stream<E>(&mut self, err: E) -> Option<Stream> {
        let stream = (self.used_errors_mask | 1).trailing_ones() as UsedErrorsMask;
        if stream as usize - 1 == ERROR_COUNT {
            return None;
        }
        debug_assert!(!self.is_full());
        // Safety: `∀x ∈ uint (x | 1).trailing_ones() > 0`
        let stream = unsafe { Stream::new_uncheked(stream as u8) };
        self.used_errors_mask |= stream.mask();
        let place = self.place_of_stream_mut(stream);
        // Safety: `place` is valid for writes, big enough and aligned enough
        // due to asserts and construction.
        unsafe { ptr::write(place, err) };
        Some(stream)
    }

    // merge i-1 and i if both are consequtive offsets and from the same stream
    #[inline(always)]
    fn merge_offset(&mut self, i: usize, s2: Stream, b2: *const u8, l2: u16) -> Option<()> {
        let a = i.checked_sub(1)?;
        if self.streams.get(a)?.as_ref()? != &s2 {
            return None;
        }
        if self.lens[a] & FrameEntry::RANGE == 0 || l2 & FrameEntry::RANGE == 0 {
            return None;
        }
        let b1 = self.bases[a] as usize;
        let b2 = b2 as usize;
        let l1 = self.lens[a] & !FrameEntry::RANGE;
        let l2 = l2 & !FrameEntry::RANGE;
        if b1 + l1 as usize != b2 {
            return None;
        }
        self.lens[a] = (l1 + l2).min(FrameEntry::MAX_LEN) | FrameEntry::RANGE;
        Some(())
    }

    /// # Safety
    /// Ensure `E` is stored where `streams` point
    pub unsafe fn remove_errors<E>(&mut self, streams: &[Option<Stream>]) {
        let mut delete_mask = 0;

        // drop errors

        for stream in streams.iter().copied().filter_map(identity) {
            if self.used_errors_mask & stream.mask() == 0 {
                // Helps with duplicates in `streams`.
                continue;
            }
            self.used_errors_mask &= !stream.mask();
            delete_mask |= stream.mask();
            let place = self.place_of_stream_mut::<E>(stream);
            // Safety:
            //  - mask guarantees that there is *something* there
            //  - caller guarantees that `E` is stored there
            unsafe { ptr::drop_in_place(place) };
        }

        // remove frames

        let mut out_i = 0;
        for i in 0..self.entries {
            let s = self.streams[i].expect("Must be initialized");
            if s.mask() & delete_mask == 0 {
                // note: if in future we allow concurrent writes to the format buffer
                //       from different streams, we would need to `merge_offset` here too
                self.streams[out_i] = Some(s);
                self.bases[out_i] = self.bases[i];
                self.lens[out_i] = self.lens[i];
                out_i += 1;
            }
        }
        self.null(out_i..self.entries);
        self.entries = out_i;

        // defragment format buffer

        let format_buf = &mut self.format_buffer.inner;
        self.format_pos = 0;
        for i in 0..self.entries {
            let FrameEntry::Offset(_, b, l) = Self::get_entry(
                self.streams[i].expect("Must be initialized"),
                self.bases[i],
                self.lens[i],
            ) else {
                continue;
            };
            if b != self.format_pos {
                debug_assert!(b > self.format_pos);
                format_buf.copy_within(b..b + l, self.format_pos);
                self.bases[i] = ptr::without_provenance(self.format_pos);
            }
            self.format_pos += l;
        }
    }

    #[allow(dead_code)]
    pub fn merge_stream(&mut self, s1: Stream, s2: Stream) -> Stream {
        _ = (s1, s2);
        todo!()
    }
}

impl Write for FrameBuilder<'_> {
    fn write_fmt(&mut self, args: fmt::Arguments<'_>) -> fmt::Result {
        if let Some(s) = args.as_str() {
            let entry = FrameEntry::from_static_str(self.1, s);
            Ok(self.0.push_entry(entry))
        } else {
            core::fmt::write(self, args)
        }
    }
    fn write_str(&mut self, s: &str) -> fmt::Result {
        #[cfg(feature = "unsafe-static-str-ranges")]
        if let Some(s) = crate::unsafe_static_str_ranges::try_to_static(s) {
            let entry = FrameEntry::from_static_str(self.1, s);
            self.0.push_entry(entry);
            return Ok(());
        }

        // todo: on cortex-m we can also check if the ptr is in data
        //       and assume it's 'static, so avoid copying
        let base = self.0.format_pos;
        let buf = &mut self.0.format_buffer.inner[base..];
        // or maybe truncate instead of error?
        let buf = buf.get_mut(..s.len()).ok_or(fmt::Error)?;
        buf.copy_from_slice(s.as_bytes());
        let entry = FrameEntry::Offset(self.1, base, s.len());
        self.0.format_pos += s.len();
        self.0.push_entry(entry);
        Ok(())
    }
}

impl FrameEntry {
    const EOF: u16 = u16::MAX;
    const MERGE: u16 = u16::MAX - 1;
    const RANGE: u16 = 0b1000_0000_0000_0000;
    const MAX_LEN: u16 = 0x7FF0;

    pub const fn is_end_of_frame(&self) -> bool {
        matches!(self, FrameEntry::EndOfFrame(_))
    }

    pub const fn from_static_str(stream: Stream, string: &'static str) -> Self {
        let len = string.len();
        Self::Static(stream, string.as_ptr(), len)
    }

    pub const fn stream(&self) -> Stream {
        match self {
            FrameEntry::Static(s, _, _)
            | FrameEntry::Offset(s, _, _)
            | FrameEntry::Merge(s, _)
            | FrameEntry::EndOfFrame(s) => *s,
        }
    }

    /// # Safety
    /// Ensure that if `self` is `Static`, pointer and length create a slice
    /// valid for reads to utf-8 string
    pub unsafe fn resolve<'a>(&self, buf: &'a [u8]) -> &'a str {
        let (b, l) = match self {
            FrameEntry::Static(_, b, l) => (*b, *l),
            FrameEntry::Offset(_, b, l) => (buf[*b..][..*l].as_ptr(), *l),
            FrameEntry::Merge(_, _) | FrameEntry::EndOfFrame(_) => return "",
        };
        str::from_utf8(unsafe { core::slice::from_raw_parts(b, l) }).unwrap_or("<invalid utf-8>")
    }
}
