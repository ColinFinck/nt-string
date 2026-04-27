// Copyright 2023 Colin Finck <colin@reactos.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use core::cmp::Ordering;
use core::mem;

use widestring::U16CStr;

use crate::error::{NtStringError, Result};

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

pub(crate) fn check_from_u16(buffer: &[u16]) -> Result<u16> {
    let elements = buffer.len();
    let length_usize = elements
        .checked_mul(mem::size_of::<u16>())
        .ok_or(NtStringError::BufferSizeExceedsU16)?;
    let length = u16::try_from(length_usize).map_err(|_| NtStringError::BufferSizeExceedsU16)?;
    Ok(length)
}

pub(crate) fn check_from_u16_until_nul(buffer: &[u16]) -> Result<(u16, u16)> {
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

    Ok((length, maximum_length))
}

pub(crate) fn check_from_u16_cstr(u16cstr: &U16CStr) -> Result<(u16, u16)> {
    let buffer = u16cstr.as_slice_with_nul();

    // Include the terminating NUL character in `maximum_length` ...
    let maximum_length_in_elements = buffer.len();
    let maximum_length_in_bytes = maximum_length_in_elements
        .checked_mul(mem::size_of::<u16>())
        .ok_or(NtStringError::BufferSizeExceedsU16)?;
    let maximum_length =
        u16::try_from(maximum_length_in_bytes).map_err(|_| NtStringError::BufferSizeExceedsU16)?;

    // ... but not in `length`
    debug_assert!(maximum_length >= mem::size_of::<u16>() as u16);
    let length = maximum_length - mem::size_of::<u16>() as u16;

    Ok((length, maximum_length))
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
