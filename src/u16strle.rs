// Copyright 2023 Colin Finck <colin@reactos.org>
// SPDX-License-Identifier: MIT OR Apache-2.0
//
//! Interface around byte slices of UTF-16 (little-endian) strings.

use core::char;
use core::cmp::Ordering;
use core::fmt;

use crate::helpers::cmp_iter;

#[cfg(feature = "alloc")]
use {
    crate::error::Result,
    alloc::string::String,
    alloc::vec::Vec,
    widestring::{decode_utf16, decode_utf16_lossy, U16String},
};

/// Byte slice treated as a serialized UTF-16 (little-endian) string.
///
/// UTF-16 little-endian is the on-disk format that Windows uses for almost all strings.
/// `U16StrLe` allows to work with this format directly without creating a copy or performing a conversion first.
///
/// The encoding is expected to be UTF-16 (or the UCS-2 subset for Windows NT 4.0 and earlier).
/// However, this type will happily accept any byte, and only cares about the encoding when converting or displaying.
#[derive(Clone, Debug, Eq)]
pub struct U16StrLe<'a>(pub &'a [u8]);

impl<'a> U16StrLe<'a> {
    /// Returns `true` if `self` has a length of zero bytes.
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the length of `self`.
    ///
    /// This length is in bytes, not characters! In other words,
    /// it may not be what a human considers the length of the string.
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    /// Attempts to copy `self` to a new owned `String`.
    /// Returns `Ok(String)` if all characters could be converted successfully or `DecodeUtf16Error` otherwise.
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn to_string(&self) -> Result<String> {
        decode_utf16(self.u16_iter())
            .collect::<Result<String, _>>()
            .map_err(Into::into)
    }

    /// Copies `self` to a new owned `String`, replacing invalid data with the replacement character (U+FFFD).
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn to_string_lossy(&self) -> String {
        decode_utf16_lossy(self.u16_iter()).collect()
    }

    /// Copies `self` to a new owned [`widestring::U16String`].
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn to_ustring(&self) -> U16String {
        U16String::from_vec(self.u16_iter().collect::<Vec<u16>>())
    }

    /// Returns an iterator over the [`u16`] codepoints of this string.
    ///
    /// The codepoints may or may not be valid UTF-16 codepoints.
    /// This function does not validate them.
    pub fn u16_iter(&'a self) -> impl Iterator<Item = u16> + 'a {
        self.0
            .chunks_exact(2)
            .map(|two_bytes| u16::from_le_bytes(two_bytes.try_into().unwrap()))
    }
}

impl<'a> fmt::Display for U16StrLe<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let utf16_iter =
            char::decode_utf16(self.u16_iter()).map(|x| x.unwrap_or(char::REPLACEMENT_CHARACTER));

        for single_char in utf16_iter {
            single_char.fmt(f)?;
        }

        Ok(())
    }
}

impl<'a> Ord for U16StrLe<'a> {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_iter(self.u16_iter(), other.u16_iter())
    }
}

impl<'a, 'b> PartialEq<U16StrLe<'a>> for U16StrLe<'b> {
    /// Checks that two strings are a (case-sensitive!) match.
    fn eq(&self, other: &U16StrLe<'a>) -> bool {
        self.0 == other.0
    }
}

impl<'a> PartialEq<str> for U16StrLe<'a> {
    fn eq(&self, other: &str) -> bool {
        cmp_iter(self.u16_iter(), other.encode_utf16()) == Ordering::Equal
    }
}

impl<'a> PartialEq<U16StrLe<'a>> for str {
    fn eq(&self, other: &U16StrLe<'a>) -> bool {
        cmp_iter(self.encode_utf16(), other.u16_iter()) == Ordering::Equal
    }
}

impl<'a> PartialEq<&str> for U16StrLe<'a> {
    fn eq(&self, other: &&str) -> bool {
        cmp_iter(self.u16_iter(), other.encode_utf16()) == Ordering::Equal
    }
}

impl<'a> PartialEq<U16StrLe<'a>> for &str {
    fn eq(&self, other: &U16StrLe<'a>) -> bool {
        cmp_iter(self.encode_utf16(), other.u16_iter()) == Ordering::Equal
    }
}

impl<'a, 'b> PartialOrd<U16StrLe<'a>> for U16StrLe<'b> {
    fn partial_cmp(&self, other: &U16StrLe<'a>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a> PartialOrd<str> for U16StrLe<'a> {
    fn partial_cmp(&self, other: &str) -> Option<Ordering> {
        Some(cmp_iter(self.u16_iter(), other.encode_utf16()))
    }
}

impl<'a> PartialOrd<U16StrLe<'a>> for str {
    fn partial_cmp(&self, other: &U16StrLe<'a>) -> Option<Ordering> {
        Some(cmp_iter(self.encode_utf16(), other.u16_iter()))
    }
}

impl<'a> PartialOrd<&str> for U16StrLe<'a> {
    fn partial_cmp(&self, other: &&str) -> Option<Ordering> {
        Some(cmp_iter(self.u16_iter(), other.encode_utf16()))
    }
}

impl<'a> PartialOrd<U16StrLe<'a>> for &str {
    fn partial_cmp(&self, other: &U16StrLe<'a>) -> Option<Ordering> {
        Some(cmp_iter(self.encode_utf16(), other.u16_iter()))
    }
}
