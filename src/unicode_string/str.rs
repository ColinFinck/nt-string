// Copyright 2023 Colin Finck <colin@reactos.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use core::cmp::Ordering;
use core::iter::Copied;
use core::marker::PhantomData;
use core::slice::Iter;
use core::{fmt, mem, slice};

use widestring::{U16CStr, U16Str};

use crate::error::{NtStringError, Result};
use crate::helpers::{cmp_iter, RawNtString};

use super::iter::{Chars, CharsLossy};

/// An immutable reference to a `UNICODE_STRING` (equivalent of `&str`).
///
/// See the [module-level documentation](super) for more details.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct NtUnicodeStr<'a> {
    raw: RawNtString<*const u16>,
    _lifetime: PhantomData<&'a ()>,
}

impl<'a> NtUnicodeStr<'a> {
    /// Returns a `*const NtUnicodeStr` pointer
    /// (mainly for non-Rust interfaces that expect an immutable `UNICODE_STRING*`).
    pub fn as_ptr(&self) -> *const Self {
        self as *const Self
    }

    /// Returns a slice to the raw [`u16`] codepoints of the string.
    pub fn as_slice(&self) -> &'a [u16] {
        unsafe { slice::from_raw_parts(self.raw.buffer, self.len_in_elements()) }
    }

    /// Returns a [`U16Str`] reference for this string.
    ///
    /// The [`U16Str`] will only contain the characters and not the NUL terminator.
    pub fn as_u16str(&self) -> &'a U16Str {
        U16Str::from_slice(self.as_slice())
    }

    /// Returns the capacity (also known as "maximum length") of this string, in bytes.
    pub fn capacity(&self) -> u16 {
        self.raw.maximum_length
    }

    /// Returns the capacity (also known as "maximum length") of this string, in elements.
    #[allow(unused)]
    pub(crate) fn capacity_in_elements(&self) -> usize {
        usize::from(self.raw.maximum_length) / mem::size_of::<u16>()
    }

    /// Returns an iterator over the [`char`]s of this string.
    ///
    /// As the string may contain invalid UTF-16 characters (unpaired surrogates), the returned iterator is an
    /// iterator over `Result<char>`.
    /// Unpaired surrogates are returned as an [`NtStringError::UnpairedUtf16Surrogate`] error.
    /// If you would like a lossy iterator over [`char`]s directly, use [`chars_lossy`] instead.
    ///
    /// [`chars_lossy`]: Self::chars_lossy
    pub fn chars(&self) -> Chars {
        Chars::new(self)
    }

    /// Returns an iterator over the [`char`]s of this string.
    ///
    /// Any invalid UTF-16 characters (unpaired surrogates) are automatically replaced by
    /// [`U+FFFD REPLACEMENT CHARACTER`] (�).
    /// If you would like to treat them differently, use [`chars`] instead.
    ///
    /// [`chars`]: Self::chars
    /// [`U+FFFD REPLACEMENT CHARACTER`]: std::char::REPLACEMENT_CHARACTER
    pub fn chars_lossy(&self) -> CharsLossy {
        CharsLossy::new(self)
    }

    /// Creates an [`NtUnicodeStr`] from a [`u16`] string buffer, a byte length of the string,
    /// and a buffer capacity in bytes (also known as "maximum length").
    ///
    /// The string is expected to consist of valid UTF-16 characters.
    /// The buffer may or may not be NUL-terminated.
    /// In any case, `length` does NOT include the terminating NUL character.
    ///
    /// This function is `unsafe` and you are advised to use any of the safe `try_from_*`
    /// functions over this one if possible.
    ///
    /// # Safety
    ///
    /// Behavior is undefined if any of the following conditions are violated:
    ///
    /// * `length` must be less than or equal to `maximum_length`.
    /// * `buffer` must be valid for at least `maximum_length` bytes.
    /// * `buffer` must point to `length` consecutive properly initialized bytes.
    /// * `buffer` must be valid for the duration of lifetime `'a`.
    ///
    /// [`try_from_u16`]: Self::try_from_u16
    /// [`try_from_u16_until_nul`]: Self::try_from_u16_until_nul
    pub const unsafe fn from_raw_parts(
        buffer: *const u16,
        length: u16,
        maximum_length: u16,
    ) -> Self {
        debug_assert!(length <= maximum_length);

        Self {
            raw: RawNtString {
                length,
                maximum_length,
                buffer,
            },
            _lifetime: PhantomData,
        }
    }

    /// Returns `true` if this string has a length of zero, and `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.raw.length == 0
    }

    /// Returns the length of this string, in bytes.
    ///
    /// Note that a single character may occupy more than one byte.
    /// In other words, the returned value might not be what a human considers the length of the string.
    pub fn len(&self) -> u16 {
        self.raw.length
    }

    /// Returns the length of this string, in elements.
    ///
    /// Note that a single character may occupy more than one element.
    /// In other words, the returned value might not be what a human considers the length of the string.
    pub(crate) fn len_in_elements(&self) -> usize {
        usize::from(self.raw.length) / mem::size_of::<u16>()
    }

    /// Returns the remaining capacity of this string, in bytes.
    #[allow(unused)]
    pub(crate) fn remaining_capacity(&self) -> u16 {
        debug_assert!(self.raw.maximum_length >= self.raw.length);
        self.raw.maximum_length - self.raw.length
    }

    /// Creates an [`NtUnicodeStr`] from an existing [`u16`] string buffer without a terminating NUL character.
    ///
    /// The string is expected to consist of valid UTF-16 characters.
    ///
    /// The given buffer becomes the internal buffer of the [`NtUnicodeStr`] and therefore won't be NUL-terminated.
    /// See the [module-level documentation](super) for the implications of that.
    ///
    /// This function has *O*(1) complexity.
    ///
    /// If you have a NUL-terminated buffer, either use [`try_from_u16_until_nul`] or convert from a [`U16CStr`]
    /// using the corresponding [`TryFrom`] implementation.
    ///
    /// [`try_from_u16_until_nul`]: Self::try_from_u16_until_nul
    pub fn try_from_u16(buffer: &'a [u16]) -> Result<Self> {
        let elements = buffer.len();
        let length_usize = elements
            .checked_mul(mem::size_of::<u16>())
            .ok_or(NtStringError::BufferSizeExceedsU16)?;
        let length =
            u16::try_from(length_usize).map_err(|_| NtStringError::BufferSizeExceedsU16)?;

        Ok(Self {
            raw: RawNtString {
                length,
                maximum_length: length,
                buffer: buffer.as_ptr(),
            },
            _lifetime: PhantomData,
        })
    }

    /// Creates an [`NtUnicodeStr`] from an existing [`u16`] string buffer that contains at least one NUL character.
    ///
    /// The string is expected to consist of valid UTF-16 characters.
    ///
    /// The string will be terminated at the NUL character.
    /// An [`NtStringError::NulNotFound`] error is returned if no NUL character could be found.
    /// As a consequence, this function has *O*(*n*) complexity.
    ///
    /// The resulting internal `buffer` of [`NtUnicodeStr`] will be NUL-terminated.
    /// See the [module-level documentation](super) for the implications of that.
    ///
    /// Use [`try_from_u16`] if you have a buffer that is not NUL-terminated.
    /// You can also convert from a NUL-terminated [`U16CStr`] in *O*(1) via the corresponding [`TryFrom`] implementation.
    ///
    /// [`try_from_u16`]: Self::try_from_u16
    pub fn try_from_u16_until_nul(buffer: &'a [u16]) -> Result<Self> {
        let length;
        let maximum_length;

        match buffer.iter().position(|x| *x == 0) {
            Some(nul_pos) => {
                // Include the terminating NUL character in `maximum_length` ...
                let maximum_elements = nul_pos
                    .checked_add(1)
                    .ok_or(NtStringError::BufferSizeExceedsU16)?;
                let maximum_length_usize = maximum_elements
                    .checked_mul(mem::size_of::<u16>())
                    .ok_or(NtStringError::BufferSizeExceedsU16)?;
                maximum_length = u16::try_from(maximum_length_usize)
                    .map_err(|_| NtStringError::BufferSizeExceedsU16)?;

                // ... but not in `length`
                length = maximum_length - mem::size_of::<u16>() as u16;
            }
            None => return Err(NtStringError::NulNotFound),
        };

        Ok(Self {
            raw: RawNtString {
                length,
                maximum_length,
                buffer: buffer.as_ptr(),
            },
            _lifetime: PhantomData,
        })
    }

    pub(crate) fn u16_iter(&'a self) -> Copied<Iter<'a, u16>> {
        self.as_slice().iter().copied()
    }
}

impl<'a> fmt::Display for NtUnicodeStr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for single_char in self.chars_lossy() {
            single_char.fmt(f)?;
        }

        Ok(())
    }
}

impl<'a> Eq for NtUnicodeStr<'a> {}

impl<'a> Ord for NtUnicodeStr<'a> {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_iter(self.u16_iter(), other.u16_iter())
    }
}

impl<'a, 'b> PartialEq<NtUnicodeStr<'a>> for NtUnicodeStr<'b> {
    /// Checks that two strings are a (case-sensitive!) match.
    fn eq(&self, other: &NtUnicodeStr<'a>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<'a> PartialEq<str> for NtUnicodeStr<'a> {
    fn eq(&self, other: &str) -> bool {
        cmp_iter(self.u16_iter(), other.encode_utf16()) == Ordering::Equal
    }
}

impl<'a> PartialEq<NtUnicodeStr<'a>> for str {
    fn eq(&self, other: &NtUnicodeStr<'a>) -> bool {
        cmp_iter(self.encode_utf16(), other.u16_iter()) == Ordering::Equal
    }
}

impl<'a> PartialEq<&str> for NtUnicodeStr<'a> {
    fn eq(&self, other: &&str) -> bool {
        cmp_iter(self.u16_iter(), other.encode_utf16()) == Ordering::Equal
    }
}

impl<'a> PartialEq<NtUnicodeStr<'a>> for &str {
    fn eq(&self, other: &NtUnicodeStr<'a>) -> bool {
        cmp_iter(self.encode_utf16(), other.u16_iter()) == Ordering::Equal
    }
}

impl<'a> PartialOrd for NtUnicodeStr<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a> PartialOrd<str> for NtUnicodeStr<'a> {
    fn partial_cmp(&self, other: &str) -> Option<Ordering> {
        Some(cmp_iter(self.u16_iter(), other.encode_utf16()))
    }
}

impl<'a> PartialOrd<NtUnicodeStr<'a>> for str {
    fn partial_cmp(&self, other: &NtUnicodeStr<'a>) -> Option<Ordering> {
        Some(cmp_iter(self.encode_utf16(), other.u16_iter()))
    }
}

impl<'a> PartialOrd<&str> for NtUnicodeStr<'a> {
    fn partial_cmp(&self, other: &&str) -> Option<Ordering> {
        Some(cmp_iter(self.u16_iter(), other.encode_utf16()))
    }
}

impl<'a> PartialOrd<NtUnicodeStr<'a>> for &str {
    fn partial_cmp(&self, other: &NtUnicodeStr<'a>) -> Option<Ordering> {
        Some(cmp_iter(self.encode_utf16(), other.u16_iter()))
    }
}

impl<'a> TryFrom<&'a U16CStr> for NtUnicodeStr<'a> {
    type Error = NtStringError;

    /// Converts a [`U16CStr`] reference into an [`NtUnicodeStr`].
    ///
    /// The internal buffer will be NUL-terminated.
    /// See the [module-level documentation](super) for the implications of that.
    fn try_from(value: &'a U16CStr) -> Result<Self> {
        let buffer = value.as_slice_with_nul();

        // Include the terminating NUL character in `maximum_length` ...
        let maximum_length_in_elements = buffer.len();
        let maximum_length_in_bytes = maximum_length_in_elements
            .checked_mul(mem::size_of::<u16>())
            .ok_or(NtStringError::BufferSizeExceedsU16)?;
        let maximum_length = u16::try_from(maximum_length_in_bytes)
            .map_err(|_| NtStringError::BufferSizeExceedsU16)?;

        // ... but not in `length`
        debug_assert!(maximum_length >= mem::size_of::<u16>() as u16);
        let length = maximum_length - mem::size_of::<u16>() as u16;

        Ok(Self {
            raw: RawNtString {
                length,
                maximum_length,
                buffer: buffer.as_ptr(),
            },
            _lifetime: PhantomData,
        })
    }
}

impl<'a> TryFrom<&'a U16Str> for NtUnicodeStr<'a> {
    type Error = NtStringError;

    /// Converts a [`U16Str`] reference into an [`NtUnicodeStr`].
    ///
    /// The internal buffer will NOT be NUL-terminated.
    /// See the [module-level documentation](super) for the implications of that.
    fn try_from(value: &'a U16Str) -> Result<Self> {
        Self::try_from_u16(value.as_slice())
    }
}
