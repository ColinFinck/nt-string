// Copyright 2023 Colin Finck <colin@reactos.org>
// SPDX-License-Identifier: MIT OR Apache-2.0
//
//! Iterator implementations for [`NtUnicodeStr`].

use core::iter::{Copied, FusedIterator};
use core::slice::Iter;

use widestring::iter::{DecodeUtf16, DecodeUtf16Lossy};
use widestring::{decode_utf16, decode_utf16_lossy};

use super::NtUnicodeStr;
use crate::error::Result;

/// An iterator over the UTF-16 decoded [`char`]s of [`NtUnicodeStr`],
/// which returns an error for unparsed surrogates.
///
/// This struct is created by the [`NtUnicodeStr::chars`] method.
///
/// [`NtUnicodeStr::chars`]: crate::unicode_string::NtUnicodeStr::chars
#[derive(Clone, Debug)]
pub struct Chars<'a> {
    iter: DecodeUtf16<Copied<Iter<'a, u16>>>,
}

impl<'a> Chars<'a> {
    pub(crate) fn new(unicode_str: &'a NtUnicodeStr) -> Self {
        Self {
            iter: decode_utf16(unicode_str.u16_iter()),
        }
    }
}

impl<'a> Iterator for Chars<'a> {
    type Item = Result<char>;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.iter.next()?;
        Some(result.map_err(Into::into))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a> FusedIterator for Chars<'a> {}

impl<'a> DoubleEndedIterator for Chars<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let result = self.iter.next_back()?;
        Some(result.map_err(Into::into))
    }
}

/// An iterator over the UTF-16 decoded [`char`]s of [`NtUnicodeStr`],
/// which automatically replaces unparsed surrogates by [`U+FFFD REPLACEMENT CHARACTER`] (�).
///
/// This struct is created by the [`NtUnicodeStr::chars_lossy`] method.
///
/// [`NtUnicodeStr::chars_lossy`]: crate::unicode_string::NtUnicodeStr::chars_lossy
/// [`U+FFFD REPLACEMENT CHARACTER`]: std::char::REPLACEMENT_CHARACTER
#[derive(Clone, Debug)]
pub struct CharsLossy<'a> {
    iter: DecodeUtf16Lossy<Copied<Iter<'a, u16>>>,
}

impl<'a> CharsLossy<'a> {
    pub(crate) fn new(unicode_str: &'a NtUnicodeStr) -> Self {
        Self {
            iter: decode_utf16_lossy(unicode_str.u16_iter()),
        }
    }
}

impl<'a> Iterator for CharsLossy<'a> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a> FusedIterator for CharsLossy<'a> {}

impl<'a> DoubleEndedIterator for CharsLossy<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}
