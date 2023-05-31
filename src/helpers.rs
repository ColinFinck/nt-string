// Copyright 2023 Colin Finck <colin@reactos.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use core::cmp::Ordering;

/// Generic memory layout unified for `ANSI_STRING`, `OEM_STRING`, `UNICODE_STRING`,
/// in their mutable and immutable versions.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub(crate) struct RawNtString<T> {
    /// Used size of `buffer`, in bytes
    pub(crate) length: u16,
    /// Allocated size of `buffer`, in bytes
    pub(crate) maximum_length: u16,
    /// String buffer
    pub(crate) buffer: T,
}

/// Compare any two `u16` iterators and return an [`Ordering`] value.
///
/// Can be used to implement `cmp`/`partial_cmp` and `eq`/`partial_eq`.
pub(crate) fn cmp_iter<TI, OI>(mut this_iter: TI, mut other_iter: OI) -> Ordering
where
    TI: Iterator<Item = u16>,
    OI: Iterator<Item = u16>,
{
    loop {
        match (this_iter.next(), other_iter.next()) {
            (Some(this_word), Some(other_word)) => {
                // We have two u16 words to compare.
                if this_word != other_word {
                    return this_word.cmp(&other_word);
                }
            }
            (Some(_), None) => {
                // `this_iter` is longer than `other_iter` but otherwise equal.
                return Ordering::Greater;
            }
            (None, Some(_)) => {
                // `other_iter` is longer than `this_iter` but otherwise equal.
                return Ordering::Less;
            }
            (None, None) => {
                // We made it to the end of both strings, so they must be equal.
                return Ordering::Equal;
            }
        }
    }
}
