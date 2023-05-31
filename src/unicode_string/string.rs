// Copyright 2023 Colin Finck <colin@reactos.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use ::alloc::alloc::{self, Layout};
use ::alloc::string::String;
use widestring::{U16CStr, U16Str};

use core::cmp::Ordering;
use core::iter::once;
use core::ops::{Add, AddAssign, Deref, DerefMut};
use core::{fmt, mem, ptr};

use crate::error::{NtStringError, Result};
use crate::helpers::RawNtString;
use crate::traits::TryExtend;

use super::{impl_eq, impl_partial_cmp, NtUnicodeStr, NtUnicodeStrMut};

/// An allocated, owned, and growable variant of `UNICODE_STRING` (equivalent of [`String`]).
///
/// See the [module-level documentation](super) for more details.
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[derive(Debug)]
#[repr(transparent)]
pub struct NtUnicodeString {
    raw: RawNtString<*mut u16>,
}

impl NtUnicodeString {
    /// Creates an empty [`NtUnicodeString`].
    ///
    /// This operation won't allocate any buffer.
    /// Therefore, length and capacity will both be zero.
    pub fn new() -> Self {
        Self {
            raw: RawNtString {
                length: 0,
                maximum_length: 0,
                buffer: ptr::null_mut(),
            },
        }
    }

    /// Returns a mutable [`NtUnicodeStrMut`] reference for this string.
    pub fn as_unicode_str_mut(&mut self) -> &mut NtUnicodeStrMut<'static> {
        self.deref_mut()
    }

    fn layout(&self) -> Layout {
        Layout::array::<u16>(self.capacity_in_elements()).unwrap()
    }

    /// Creates an [`NtUnicodeString`] from an existing [`u16`] string buffer without a terminating NUL character.
    ///
    /// The string is expected to consist of valid UTF-16 characters.
    ///
    /// The given buffer becomes the internal buffer of the [`NtUnicodeString`] and therefore won't be NUL-terminated.
    /// See the [module-level documentation](super) for the implications of that.
    ///
    /// This function has *O*(1) complexity.
    ///
    /// If you have a NUL-terminated buffer, either use [`try_from_u16_until_nul`] or convert from a [`U16CStr`]
    /// using the corresponding [`TryFrom`] implementation.
    ///
    /// [`try_from_u16_until_nul`]: Self::try_from_u16_until_nul
    pub fn try_from_u16(buffer: &[u16]) -> Result<Self> {
        let unicode_str = NtUnicodeStr::try_from_u16(buffer)?;
        Ok(Self::from(&unicode_str))
    }

    /// Creates an [`NtUnicodeString`] from an existing [`u16`] string buffer that contains at least one NUL character.
    ///
    /// The string is expected to consist of valid UTF-16 characters.
    ///
    /// The string will be terminated at the NUL character.
    /// An [`NtStringError::NulNotFound`] error is returned if no NUL character could be found.
    /// As a consequence, this function has *O*(*n*) complexity.
    ///
    /// The resulting internal `buffer` of [`NtUnicodeString`] will be NUL-terminated.
    /// See the [module-level documentation](super) for the implications of that.
    ///
    /// Use [`try_from_u16`] if you have a buffer that is not NUL-terminated.
    /// You can also convert from a NUL-terminated [`U16CStr`] in *O*(1) via the corresponding [`TryFrom`] implementation.
    ///
    /// [`try_from_u16`]: Self::try_from_u16
    pub fn try_from_u16_until_nul(buffer: &[u16]) -> Result<Self> {
        let unicode_str = NtUnicodeStr::try_from_u16_until_nul(buffer)?;
        Ok(Self::from(&unicode_str))
    }

    /// Appends the given [`char`] to the end of this string.
    ///
    /// Returns an [`NtStringError::BufferSizeExceedsU16`] error if the resulting string would exceed
    /// 65532 bytes.
    /// This is due to the fact that a `UNICODE_STRING` internally uses a 16-bit field to store the length.
    /// Additionally, this function allocates one more character for NUL termination of the internal
    /// buffer.
    /// See the [module-level documentation](super) for the implications of that.
    ///
    /// Note that every UTF-16 character consumes 2 or 4 bytes.
    pub fn try_push(&mut self, c: char) -> Result<()> {
        // Determine the required additional capacity.
        //
        // Add one element for the terminating NUL character
        // (for applications that mistakenly treat the buffer of a Unicode String as a NUL-terminated string).
        let encoded_length = c.len_utf16();
        let additional_elements = encoded_length + 1;

        // Reserve the additional capacity.
        let additional = (additional_elements * mem::size_of::<u16>()) as u16;
        self.try_reserve(additional)?;

        // Encode the character as UTF-16 at the end of the buffer.
        let end_index = self.len_in_elements();
        self.raw.length += additional;

        let dest_slice = &mut self.as_mut_slice()[end_index..];
        c.encode_utf16(dest_slice);

        // NUL-terminate it.
        dest_slice[encoded_length] = 0;

        // Set the final length (without including the terminating NUL character).
        self.raw.length -= mem::size_of::<u16>() as u16;

        Ok(())
    }

    /// Appends the given string slice to the end of this string.
    ///
    /// Returns an [`NtStringError::BufferSizeExceedsU16`] error if the resulting string would exceed
    /// 65532 bytes.
    /// This is due to the fact that a `UNICODE_STRING` internally uses a 16-bit field to store the length.
    /// Additionally, this function allocates one more character for NUL termination of the internal
    /// buffer.
    /// See the [module-level documentation](super) for the implications of that.
    ///
    /// Note that every UTF-16 character consumes 2 or 4 bytes.
    pub fn try_push_str(&mut self, s: &str) -> Result<()> {
        // Determine the required additional capacity.
        //
        // Add one element for the terminating NUL character
        // (for applications that mistakenly treat the buffer of a Unicode String as a NUL-terminated string).
        let additional_elements = s
            .encode_utf16()
            .count()
            .checked_add(1)
            .ok_or(NtStringError::BufferSizeExceedsU16)?;

        // Reserve the additional capacity.
        let additional_bytes = additional_elements
            .checked_mul(mem::size_of::<u16>())
            .ok_or(NtStringError::BufferSizeExceedsU16)?;
        let additional =
            u16::try_from(additional_bytes).map_err(|_| NtStringError::BufferSizeExceedsU16)?;
        self.try_reserve(additional)?;

        // Copy over the string and NUL-terminate it.
        let end_index = self.len_in_elements();
        self.raw.length += additional;

        for (string_item, utf16_item) in self.as_mut_slice()[end_index..]
            .iter_mut()
            .zip(s.encode_utf16().chain(once(0)))
        {
            *string_item = utf16_item;
        }

        // Set the final length (without the terminating NUL character).
        self.raw.length -= mem::size_of::<u16>() as u16;

        Ok(())
    }

    /// Appends the given [`u16`] string buffer (without a terminating NUL character) to the end of this string.
    ///
    /// The string is expected to consist of valid UTF-16 characters.
    ///
    /// Returns an [`NtStringError::BufferSizeExceedsU16`] error if the resulting string would exceed
    /// 65532 bytes.
    /// This is due to the fact that a `UNICODE_STRING` internally uses a 16-bit field to store the length.
    /// Additionally, this function allocates one more character for NUL termination of the internal
    /// buffer.
    /// See the [module-level documentation](super) for the implications of that.
    ///
    /// Note that every UTF-16 character consumes 2 or 4 bytes.
    ///
    /// This function has *O*(1) complexity.
    ///
    /// See [`try_push_u16_until_nul`] or [`try_push_u16cstr`] if you have a NUL-terminated buffer.
    ///
    /// [`try_push_u16_until_nul`]: Self::try_push_u16_until_nul
    /// [`try_push_u16cstr`]: Self::try_push_u16cstr
    pub fn try_push_u16(&mut self, buffer: &[u16]) -> Result<()> {
        // Determine the required additional capacity.
        //
        // Add one element for the terminating NUL character
        // (for applications that mistakenly treat the buffer of a Unicode String as a NUL-terminated string).
        let additional_elements = buffer
            .len()
            .checked_add(1)
            .ok_or(NtStringError::BufferSizeExceedsU16)?;

        // Reserve the additional capacity.
        let additional_bytes = additional_elements
            .checked_mul(mem::size_of::<u16>())
            .ok_or(NtStringError::BufferSizeExceedsU16)?;
        let additional =
            u16::try_from(additional_bytes).map_err(|_| NtStringError::BufferSizeExceedsU16)?;
        self.try_reserve(additional)?;

        // Copy over the string.
        let end_index = self.len_in_elements();
        self.raw.length += additional;

        let dest_slice = &mut self.as_mut_slice()[end_index..];
        dest_slice[..buffer.len()].copy_from_slice(buffer);

        // NUL-terminate it.
        dest_slice[buffer.len()] = 0;

        // Set the final length (without the terminating NUL character).
        self.raw.length -= mem::size_of::<u16>() as u16;

        Ok(())
    }

    /// Appends the given [`u16`] string buffer, which contains at least one NUL character,
    /// to the end of this string.
    ///
    /// The string is expected to consist of valid UTF-16 characters.
    ///
    /// The string will be terminated at the NUL character.
    /// An [`NtStringError::NulNotFound`] error is returned if no NUL character could be found.
    /// As a consequence, this function has *O*(*n*) complexity.
    ///
    /// Returns an [`NtStringError::BufferSizeExceedsU16`] error if the resulting string would exceed
    /// 65532 bytes.
    /// This is due to the fact that a `UNICODE_STRING` internally uses a 16-bit field to store the length.
    /// Additionally, this function allocates one more character for NUL termination of the internal
    /// buffer.
    /// See the [module-level documentation](super) for the implications of that.
    ///
    /// Note that every UTF-16 character consumes 2 or 4 bytes.
    ///
    /// Use [`try_push_u16`] if you have a buffer that is not NUL-terminated.
    /// You can also push a NUL-terminated [`U16CStr`] in *O*(1) via [`try_push_u16cstr`].
    ///
    /// [`try_push_u16`]: Self::try_push_u16
    /// [`try_push_u16cstr`]: Self::try_push_u16cstr
    pub fn try_push_u16_until_nul(&mut self, buffer: &[u16]) -> Result<()> {
        match buffer.iter().position(|x| *x == 0) {
            Some(nul_pos) => self.try_push_u16(&buffer[..nul_pos]),
            None => Err(NtStringError::NulNotFound),
        }
    }

    /// Appends the given [`U16CStr`] to the end of this string.
    ///
    /// Returns an [`NtStringError::BufferSizeExceedsU16`] error if the resulting string would exceed
    /// 65532 bytes.
    /// This is due to the fact that a `UNICODE_STRING` internally uses a 16-bit field to store the length.
    /// Additionally, this function allocates one more character for NUL termination of the internal
    /// buffer.
    /// See the [module-level documentation](super) for the implications of that.
    ///
    /// Note that every UTF-16 character consumes 2 or 4 bytes.
    ///
    /// This function has *O*(1) complexity.
    pub fn try_push_u16cstr(&mut self, u16cstr: &U16CStr) -> Result<()> {
        self.try_push_u16(u16cstr.as_slice())
    }

    /// Appends the given [`U16Str`] to the end of this string.
    ///
    /// Returns an [`NtStringError::BufferSizeExceedsU16`] error if the resulting string would exceed
    /// 65532 bytes.
    /// This is due to the fact that a `UNICODE_STRING` internally uses a 16-bit field to store the length.
    /// Additionally, this function allocates one more character for NUL termination of the internal
    /// buffer.
    /// See the [module-level documentation](super) for the implications of that.
    ///
    /// Note that every UTF-16 character consumes 2 or 4 bytes.
    ///
    /// This function has *O*(1) complexity.
    pub fn try_push_u16str(&mut self, u16str: &U16Str) -> Result<()> {
        self.try_push_u16(u16str.as_slice())
    }

    /// Reserves capacity for `additional` bytes more than the current length.
    ///
    /// Returns an [`NtStringError::BufferSizeExceedsU16`] error if the resulting capacity would exceed
    /// 65535 bytes.
    ///
    /// Note that every UTF-16 character consumes 2 or 4 bytes.
    pub fn try_reserve(&mut self, additional: u16) -> Result<()> {
        if self.remaining_capacity() >= additional {
            return Ok(());
        }

        let new_capacity = self
            .len()
            .checked_add(additional)
            .ok_or(NtStringError::BufferSizeExceedsU16)?;

        if self.raw.buffer.is_null() {
            self.raw.maximum_length = new_capacity;
            let new_layout = self.layout();

            self.raw.buffer = unsafe { alloc::alloc(new_layout) } as *mut u16;
        } else {
            let old_layout = self.layout();

            self.raw.buffer = unsafe {
                alloc::realloc(
                    self.raw.buffer as *mut u8,
                    old_layout,
                    usize::from(new_capacity),
                )
            } as *mut u16;

            self.raw.maximum_length = new_capacity;
        }

        Ok(())
    }

    /// Creates an empty [`NtUnicodeString`] with at least the specified capacity.
    ///
    /// This will preallocate a buffer with the given capacity.
    /// If the given capacity is `0`, no allocation will occur, and this method is identical to the [`new`] method.
    ///
    /// [`new`]: Self::new
    pub fn with_capacity(capacity: u16) -> Self {
        let mut string = Self::new();
        string.try_reserve(capacity).unwrap();
        string
    }
}

impl Add<&str> for NtUnicodeString {
    type Output = NtUnicodeString;

    fn add(mut self, rhs: &str) -> Self::Output {
        if let Err(e) = self.try_push_str(rhs) {
            panic!("{e}");
        }

        self
    }
}

impl Add<&U16CStr> for NtUnicodeString {
    type Output = NtUnicodeString;

    fn add(mut self, rhs: &U16CStr) -> Self::Output {
        if let Err(e) = self.try_push_u16cstr(rhs) {
            panic!("{e}");
        }

        self
    }
}

impl Add<&U16Str> for NtUnicodeString {
    type Output = NtUnicodeString;

    fn add(mut self, rhs: &U16Str) -> Self::Output {
        if let Err(e) = self.try_push_u16str(rhs) {
            panic!("{e}");
        }

        self
    }
}

impl AddAssign<&str> for NtUnicodeString {
    fn add_assign(&mut self, rhs: &str) {
        if let Err(e) = self.try_push_str(rhs) {
            panic!("{e}");
        }
    }
}

impl AddAssign<&U16CStr> for NtUnicodeString {
    fn add_assign(&mut self, rhs: &U16CStr) {
        if let Err(e) = self.try_push_u16cstr(rhs) {
            panic!("{e}");
        }
    }
}

impl AddAssign<&U16Str> for NtUnicodeString {
    fn add_assign(&mut self, rhs: &U16Str) {
        if let Err(e) = self.try_push_u16str(rhs) {
            panic!("{e}");
        }
    }
}

impl Clone for NtUnicodeString {
    /// Creates a copy of this [`NtUnicodeString`].
    ///
    /// This implementation keeps the original capacity.
    fn clone(&self) -> Self {
        NtUnicodeString::from(self.as_unicode_str())
    }
}

impl Default for NtUnicodeString {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for NtUnicodeString {
    // The NtUnicodeString can't be dropped while someone still holds a reference to it,
    // so the `buffer` lifetime is effectively 'static for the duration of the reference.
    type Target = NtUnicodeStrMut<'static>;

    fn deref(&self) -> &Self::Target {
        // SAFETY: `NtUnicodeStrMut` and `NtUnicodeString` have the same memory layout,
        // so we can safely transmute `NtUnicodeString` to `NtUnicodeStrMut`.
        unsafe { mem::transmute(self) }
    }
}

impl DerefMut for NtUnicodeString {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: `NtUnicodeStrMut` and `NtUnicodeString` have the same memory layout,
        // so we can safely transmute `NtUnicodeString` to `NtUnicodeStrMut`.
        unsafe { mem::transmute(self) }
    }
}

impl fmt::Display for NtUnicodeString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.deref(), f)
    }
}

impl Drop for NtUnicodeString {
    fn drop(&mut self) {
        if !self.raw.buffer.is_null() {
            let layout = self.layout();
            unsafe { alloc::dealloc(self.raw.buffer as *mut u8, layout) }
        }
    }
}

impl Eq for NtUnicodeString {}

impl From<char> for NtUnicodeString {
    /// Creates an [`NtUnicodeString`] from a single [`char`].
    fn from(c: char) -> Self {
        let mut string = Self::new();
        string.try_push(c).unwrap();
        string
    }
}

impl<'a> From<&NtUnicodeStr<'a>> for NtUnicodeString {
    /// Creates an [`NtUnicodeString`] from an existing [`NtUnicodeStr`].
    ///
    /// This implementation keeps the original capacity.
    fn from(unicode_str: &NtUnicodeStr) -> Self {
        let mut new_string = Self::with_capacity(unicode_str.capacity());

        if !unicode_str.is_empty() {
            new_string.raw.length = unicode_str.len();
            new_string
                .as_mut_slice()
                .copy_from_slice(unicode_str.as_slice());
        }

        new_string
    }
}

impl Ord for NtUnicodeString {
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(self.deref(), other.deref())
    }
}

impl_eq! { NtUnicodeString, NtUnicodeString }
impl_eq! { NtUnicodeStr<'a>, NtUnicodeString }
impl_eq! { NtUnicodeString, NtUnicodeStr<'a> }
impl_eq! { NtUnicodeStrMut<'a>, NtUnicodeString }
impl_eq! { NtUnicodeString, NtUnicodeStrMut<'a> }
impl_eq! { NtUnicodeString, str }
impl_eq! { str, NtUnicodeString }
impl_eq! { NtUnicodeString, &str }
impl_eq! { &str, NtUnicodeString }

impl_partial_cmp! { NtUnicodeString, NtUnicodeString }
impl_partial_cmp! { NtUnicodeStr<'a>, NtUnicodeString }
impl_partial_cmp! { NtUnicodeString, NtUnicodeStr<'a> }
impl_partial_cmp! { NtUnicodeStrMut<'a>, NtUnicodeString }
impl_partial_cmp! { NtUnicodeString, NtUnicodeStrMut<'a> }
impl_partial_cmp! { NtUnicodeString, str }
impl_partial_cmp! { str, NtUnicodeString }
impl_partial_cmp! { NtUnicodeString, &str }
impl_partial_cmp! { &str, NtUnicodeString }

impl TryExtend<char> for NtUnicodeString {
    type Error = NtStringError;

    fn try_extend<I: IntoIterator<Item = char>>(&mut self, iter: I) -> Result<()> {
        let iterator = iter.into_iter();
        let (lower_bound, _) = iterator.size_hint();

        // Add one element for the terminating NUL character
        // (for applications that mistakenly treat the buffer of a Unicode String as a NUL-terminated string).
        let additional_elements = lower_bound + 1;

        // Reserve the additional capacity once to save on allocations.
        let additional_bytes = u16::try_from(additional_elements * mem::size_of::<u16>())
            .map_err(|_| NtStringError::BufferSizeExceedsU16)?;
        self.try_reserve(additional_bytes)?;

        for ch in iterator {
            self.try_push(ch)?;
        }

        Ok(())
    }

    fn try_extend_one(&mut self, item: char) -> Result<()> {
        self.try_push(item)
    }
}

impl<'a> TryExtend<&'a str> for NtUnicodeString {
    type Error = NtStringError;

    fn try_extend<I: IntoIterator<Item = &'a str>>(&mut self, iter: I) -> Result<()> {
        for s in iter.into_iter() {
            self.try_push_str(s)?;
        }

        Ok(())
    }
}

impl<'a> TryExtend<&'a U16CStr> for NtUnicodeString {
    type Error = NtStringError;

    fn try_extend<I: IntoIterator<Item = &'a U16CStr>>(&mut self, iter: I) -> Result<()> {
        for s in iter.into_iter() {
            self.try_push_u16cstr(s)?;
        }

        Ok(())
    }
}

impl<'a> TryExtend<&'a U16Str> for NtUnicodeString {
    type Error = NtStringError;

    fn try_extend<I: IntoIterator<Item = &'a U16Str>>(&mut self, iter: I) -> Result<()> {
        for s in iter.into_iter() {
            self.try_push_u16str(s)?;
        }

        Ok(())
    }
}

impl TryFrom<&str> for NtUnicodeString {
    type Error = NtStringError;

    /// Converts a string slice into an owned [`NtUnicodeString`].
    ///
    /// This allocates a buffer of matching size on the heap and NUL-terminates it internally.
    /// See the [module-level documentation](super) for the implications of that.
    fn try_from(s: &str) -> Result<Self> {
        let mut string = Self::new();
        string.try_push_str(s)?;
        Ok(string)
    }
}

impl TryFrom<String> for NtUnicodeString {
    type Error = NtStringError;

    /// Converts a [`String`] into an owned [`NtUnicodeString`].
    ///
    /// This allocates a buffer of matching size on the heap and NUL-terminates it internally.
    /// See the [module-level documentation](super) for the implications of that.
    fn try_from(s: String) -> Result<Self> {
        NtUnicodeString::try_from(s.as_str())
    }
}

impl TryFrom<&String> for NtUnicodeString {
    type Error = NtStringError;

    /// Converts a [`String`] reference into an owned [`NtUnicodeString`].
    ///
    /// This allocates a buffer of matching size on the heap and NUL-terminates it internally.
    /// See the [module-level documentation](super) for the implications of that.
    fn try_from(s: &String) -> Result<Self> {
        NtUnicodeString::try_from(s.as_str())
    }
}

impl TryFrom<&U16CStr> for NtUnicodeString {
    type Error = NtStringError;

    /// Converts a [`U16CStr`] reference into an owned [`NtUnicodeString`].
    ///
    /// The internal buffer will be NUL-terminated.
    /// See the [module-level documentation](super) for the implications of that.
    fn try_from(value: &U16CStr) -> Result<Self> {
        let unicode_str = NtUnicodeStr::try_from(value)?;
        Ok(Self::from(&unicode_str))
    }
}

impl TryFrom<&U16Str> for NtUnicodeString {
    type Error = NtStringError;

    /// Converts a [`U16Str`] reference into an owned [`NtUnicodeString`].
    ///
    /// The internal buffer will NOT be NUL-terminated.
    /// See the [module-level documentation](super) for the implications of that.
    fn try_from(value: &U16Str) -> Result<Self> {
        let unicode_str = NtUnicodeStr::try_from(value)?;
        Ok(Self::from(&unicode_str))
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use crate::error::NtStringError;
    use crate::traits::TryExtend;
    use crate::unicode_string::NtUnicodeString;

    #[test]
    fn test_add() {
        let mut string = NtUnicodeString::new();
        string += "👍";
        assert_eq!(string, "👍");

        let string2 = string + "👎";
        assert_eq!(string2, "👍👎");
    }

    #[test]
    fn test_chars() {
        // Verify that ASCII characters work and allocate 2 bytes per character.
        // Verify that one more element (2 bytes) is allocated for the terminating NUL character.
        let moin = NtUnicodeString::try_from("Moin").unwrap();
        assert_eq!(moin.capacity(), 10);
        assert_eq!(moin.len(), 8);
        let vec = moin.chars_lossy().collect::<Vec<char>>();
        assert_eq!(vec, ['M', 'o', 'i', 'n']);

        // Verify that Unicode characters inside the Basic Multilingual Plane work and allocate 2 bytes per character.
        // Verify that one more element (2 bytes) is allocated for the terminating NUL character.
        let 今日は = NtUnicodeString::try_from("今日は").unwrap();
        assert_eq!(今日は.capacity(), 8);
        assert_eq!(今日は.len(), 6);
        let vec = 今日は.chars_lossy().collect::<Vec<char>>();
        assert_eq!(vec, ['今', '日', 'は']);

        // Verify that Unicode characters outside the Basic Multilingual Plane (e.g. emojis) work and allocate 4 bytes per character.
        // Verify that one more element (2 bytes) is allocated for the terminating NUL character.
        let smile = NtUnicodeString::try_from("😀").unwrap();
        assert_eq!(smile.capacity(), 6);
        assert_eq!(smile.len(), 4);
        let vec = smile.chars_lossy().collect::<Vec<char>>();
        assert_eq!(vec, ['😀']);
    }

    #[test]
    fn test_cmp() {
        let a = NtUnicodeString::try_from("a").unwrap();
        let b = NtUnicodeString::try_from("b").unwrap();
        assert!(a < b);
    }

    #[test]
    fn test_eq() {
        let hello = NtUnicodeString::try_from("Hello").unwrap();
        let hello_again = NtUnicodeString::try_from("Hello again").unwrap();
        assert_ne!(hello, hello_again);

        let mut hello_clone = hello.clone();
        assert_eq!(hello, hello_clone);

        hello_clone.try_reserve(42).unwrap();
        assert_eq!(hello, hello_clone);
    }

    #[test]
    fn test_extend_and_pop() {
        // Verify that 32766 characters still work.
        // Verify that one more element (2 bytes) is allocated for the terminating NUL character.
        let a_string = "a".repeat(32766);
        let mut string = NtUnicodeString::try_from(a_string).unwrap();
        assert_eq!(string.capacity(), 65534);
        assert_eq!(string.len(), 65532);

        // Verify that extending by a single character fails.
        assert_eq!(
            string.try_extend(Some('b')),
            Err(NtStringError::BufferSizeExceedsU16)
        );

        // Pop a character to append a new one.
        assert_eq!(string.pop(), Some(Ok('a')));
        assert_eq!(string.capacity(), 65534);
        assert_eq!(string.len(), 65530);
        string.try_extend_one('c').unwrap();
        assert_eq!(string.capacity(), 65534);
        assert_eq!(string.len(), 65532);

        // Pop two characters to append an emoji.
        assert_eq!(string.pop(), Some(Ok('c')));
        assert_eq!(string.pop(), Some(Ok('a')));
        assert_eq!(string.capacity(), 65534);
        assert_eq!(string.len(), 65528);
        string.try_extend_one('😀').unwrap();
        assert_eq!(string.capacity(), 65534);
        assert_eq!(string.len(), 65532);

        // Pop the emoji and another character to append 3 ASCII characters.
        assert_eq!(string.pop(), Some(Ok('😀')));
        assert_eq!(string.pop(), Some(Ok('a')));
        assert_eq!(string.capacity(), 65534);
        assert_eq!(string.len(), 65526);
        string.try_extend("def".chars()).unwrap();
        assert_eq!(string.capacity(), 65534);
        assert_eq!(string.len(), 65532);
    }

    #[test]
    fn test_from_u16() {
        // Verify that `try_from_u16` fails if we exceed a `u16`.
        let mut a_vec = "a".repeat(32768).encode_utf16().collect::<Vec<u16>>();
        assert_eq!(
            NtUnicodeString::try_from_u16(&a_vec),
            Err(NtStringError::BufferSizeExceedsU16)
        );

        // Verify that `try_from_u16` does not reserve any space for a terminating NUL character.
        a_vec.pop();
        let string = NtUnicodeString::try_from_u16(&a_vec).unwrap();
        assert_eq!(string.capacity(), 65534);
        assert_eq!(string.len(), 65534);

        // Verify that `try_from_u16_until_nul` does reserve space for a terminating NUL character.
        a_vec[4] = 0;
        let string = NtUnicodeString::try_from_u16_until_nul(&a_vec).unwrap();
        assert_eq!(string.capacity(), 10);
        assert_eq!(string.len(), 8);
        assert_eq!(string, "aaaa");
    }

    #[test]
    fn test_push_str() {
        let mut string = NtUnicodeString::new();
        string.try_push_str("Hey").unwrap();
        assert_eq!(string, "Hey");
        assert_eq!(string.capacity(), 8);
        assert_eq!(string.len(), 6);

        string.try_push_str("Ho").unwrap();
        assert_eq!(string, "HeyHo");
        assert_eq!(string.capacity(), 12);
        assert_eq!(string.len(), 10);
    }

    #[test]
    fn test_reserve() {
        let mut string = NtUnicodeString::new();
        assert_eq!(string.capacity(), 0);

        string.try_reserve(5).unwrap();
        assert_eq!(string.capacity(), 5);

        string.try_reserve(3).unwrap();
        assert_eq!(string.capacity(), 5);

        string.try_push_str("a").unwrap();
        assert_eq!(string, "a");
        assert_eq!(string.capacity(), 5);

        string.try_push_str("b").unwrap();
        assert_eq!(string, "ab");
        assert_eq!(string.capacity(), 6);
    }
}
