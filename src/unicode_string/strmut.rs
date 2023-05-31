// Copyright 2023 Colin Finck <colin@reactos.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use core::cmp::Ordering;
use core::marker::PhantomData;
use core::ops::Deref;
use core::{fmt, mem, slice};

use widestring::{U16CStr, U16Str};

use crate::error::Result;
use crate::helpers::RawNtString;
use crate::NtStringError;

use super::{impl_eq, impl_partial_cmp, NtUnicodeStr};

/// A mutable reference to a `UNICODE_STRING` (equivalent of `&mut str`).
///
/// See the [module-level documentation](super) for more details.
#[derive(Debug)]
#[repr(transparent)]
pub struct NtUnicodeStrMut<'a> {
    raw: RawNtString<*mut u16>,
    _lifetime: PhantomData<&'a ()>,
}

impl<'a> NtUnicodeStrMut<'a> {
    /// Returns a `*mut NtUnicodeStrMut` pointer
    /// (mainly for non-Rust interfaces that expect a mutable `UNICODE_STRING*`).
    pub fn as_mut_ptr(&mut self) -> *mut Self {
        self as *mut Self
    }

    /// Returns a mutable slice to the raw `u16` codepoints of the string.
    pub fn as_mut_slice(&mut self) -> &'a mut [u16] {
        unsafe { slice::from_raw_parts_mut(self.raw.buffer, self.len_in_elements()) }
    }

    /// Returns a mutable [`U16Str`] reference for this string.
    ///
    /// The [`U16Str`] will only contain the characters and not the NUL terminator.
    pub fn as_mut_u16str(&mut self) -> &'a U16Str {
        U16Str::from_slice_mut(self.as_mut_slice())
    }

    /// Returns an immutable [`NtUnicodeStr`] reference for this string.
    pub fn as_unicode_str(&'a self) -> &NtUnicodeStr<'a> {
        self.deref()
    }

    /// Truncates this string, removing all contents.
    ///
    /// While this means the string will have a length of zero, it does not touch its capacity.
    pub fn clear(&mut self) {
        self.raw.length = 0;
    }

    /// Creates an [`NtUnicodeStrMut`] from a [`u16`] string buffer, a byte length of the string,
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
    pub const unsafe fn from_raw_parts(buffer: *mut u16, length: u16, maximum_length: u16) -> Self {
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

    /// Removes the last character from the string and returns it.
    ///
    /// An [`NtStringError::UnpairedUtf16Surrogate`] error is returned if the last character is an unpaired surrogate.
    /// In that case, the unpaired surrogate codepoint is removed from the string anyway.
    ///
    /// `None` is returned if this string is empty.
    ///
    /// [`NtStringError::UnpairedUtf16Surrogate`]: crate::error::NtStringError::UnpairedUtf16Surrogate
    pub fn pop(&mut self) -> Option<Result<char>> {
        match self.chars().rev().next()? {
            Ok(c) => {
                self.raw.length -= (c.len_utf16() * mem::size_of::<u16>()) as u16;
                Some(Ok(c))
            }
            Err(e) => {
                // An unpaired surrogate is always a single character.
                self.raw.length -= mem::size_of::<u16>() as u16;
                Some(Err(e))
            }
        }
    }

    /// Creates an [`NtUnicodeStrMut`] from an existing [`u16`] string buffer without a terminating NUL character.
    ///
    /// The string is expected to consist of valid UTF-16 characters.
    ///
    /// The given buffer becomes the internal buffer of the [`NtUnicodeStrMut`] and therefore won't be NUL-terminated.
    /// See the [module-level documentation](super) for the implications of that.
    ///
    /// This function has *O*(1) complexity.
    ///
    /// If you have a NUL-terminated buffer, either use [`try_from_u16_until_nul`] or convert from a [`U16CStr`]
    /// using the corresponding [`TryFrom`] implementation.
    ///
    /// [`try_from_u16_until_nul`]: Self::try_from_u16_until_nul
    pub fn try_from_u16(buffer: &mut [u16]) -> Result<Self> {
        let unicode_str = NtUnicodeStr::try_from_u16(buffer)?;

        // SAFETY: `unicode_str` was created from a mutable `buffer` and
        // `NtUnicodeStr` and `NtUnicodeStrMut` have the same memory layout,
        // so we can safely transmute `NtUnicodeStr` to `NtUnicodeStrMut`.
        let unicode_str_mut = unsafe { mem::transmute(unicode_str) };

        Ok(unicode_str_mut)
    }

    /// Creates an [`NtUnicodeStrMut`] from an existing [`u16`] string buffer that contains at least one NUL character.
    ///
    /// The string is expected to consist of valid UTF-16 characters.
    ///
    /// The string will be terminated at the NUL character.
    /// An [`NtStringError::NulNotFound`] error is returned if no NUL character could be found.
    /// As a consequence, this function has *O*(*n*) complexity.
    ///
    /// The resulting internal `buffer` of [`NtUnicodeStrMut`] will be NUL-terminated.
    /// See the [module-level documentation](super) for the implications of that.
    ///
    /// Use [`try_from_u16`] if you have a buffer that is not NUL-terminated.
    /// You can also convert from a NUL-terminated [`U16CStr`] in *O*(1) via the corresponding [`TryFrom`] implementation.
    ///
    /// [`try_from_u16`]: Self::try_from_u16
    pub fn try_from_u16_until_nul(buffer: &mut [u16]) -> Result<Self> {
        let unicode_str = NtUnicodeStr::try_from_u16_until_nul(buffer)?;

        // SAFETY: `unicode_str` was created from a mutable `buffer` and
        // `NtUnicodeStr` and `NtUnicodeStrMut` have the same memory layout,
        // so we can safely transmute `NtUnicodeStr` to `NtUnicodeStrMut`.
        let unicode_str_mut = unsafe { mem::transmute(unicode_str) };

        Ok(unicode_str_mut)
    }
}

impl<'a> Deref for NtUnicodeStrMut<'a> {
    type Target = NtUnicodeStr<'a>;

    fn deref(&self) -> &Self::Target {
        // SAFETY: `NtUnicodeStr` and `NtUnicodeStrMut` have the same memory layout,
        // with the additional constraint of an immutable `buffer` pointer in `NtUnicodeStr`,
        // so we can safely transmute `NtUnicodeStrMut` to `NtUnicodeStr`.
        unsafe { mem::transmute(self) }
    }
}

impl<'a> fmt::Display for NtUnicodeStrMut<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.deref(), f)
    }
}

impl<'a> Eq for NtUnicodeStrMut<'a> {}

impl<'a> Ord for NtUnicodeStrMut<'a> {
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(self.deref(), other.deref())
    }
}

impl<'a> TryFrom<&'a mut U16CStr> for NtUnicodeStrMut<'a> {
    type Error = NtStringError;

    /// Converts a mutable [`U16CStr`] reference into an [`NtUnicodeStrMut`].
    ///
    /// The internal buffer will be NUL-terminated.
    /// See the [module-level documentation](super) for the implications of that.
    fn try_from(value: &'a mut U16CStr) -> Result<Self> {
        let unicode_str = NtUnicodeStr::try_from(&*value)?;

        // SAFETY: `unicode_str` was created from a mutable `value` and
        // `NtUnicodeStr` and `NtUnicodeStrMut` have the same memory layout,
        // so we can safely transmute `NtUnicodeStr` to `NtUnicodeStrMut`.
        let unicode_str_mut = unsafe { mem::transmute(unicode_str) };

        Ok(unicode_str_mut)
    }
}

impl<'a> TryFrom<&'a mut U16Str> for NtUnicodeStrMut<'a> {
    type Error = NtStringError;

    /// Converts a [`U16Str`] reference into an [`NtUnicodeStr`].
    ///
    /// The internal buffer will NOT be NUL-terminated.
    /// See the [module-level documentation](super) for the implications of that.
    fn try_from(value: &'a mut U16Str) -> Result<Self> {
        Self::try_from_u16(value.as_mut_slice())
    }
}

impl_eq! { NtUnicodeStrMut<'a>, NtUnicodeStrMut<'b> }
impl_eq! { NtUnicodeStr<'a>, NtUnicodeStrMut<'b> }
impl_eq! { NtUnicodeStrMut<'a>, NtUnicodeStr<'b> }
impl_eq! { NtUnicodeStrMut<'a>, str }
impl_eq! { str, NtUnicodeStrMut<'a> }
impl_eq! { NtUnicodeStrMut<'a>, &str }
impl_eq! { &str, NtUnicodeStrMut<'a> }

impl_partial_cmp! { NtUnicodeStrMut<'a>, NtUnicodeStrMut<'b> }
impl_partial_cmp! { NtUnicodeStr<'a>, NtUnicodeStrMut<'b> }
impl_partial_cmp! { NtUnicodeStrMut<'a>, NtUnicodeStr<'b> }
impl_partial_cmp! { NtUnicodeStrMut<'a>, str }
impl_partial_cmp! { str, NtUnicodeStrMut<'a> }
impl_partial_cmp! { NtUnicodeStrMut<'a>, &str }
impl_partial_cmp! { &str, NtUnicodeStrMut<'a> }
