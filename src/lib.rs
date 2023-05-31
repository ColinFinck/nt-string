// Copyright 2023 Colin Finck <colin@reactos.org>
// SPDX-License-Identifier: MIT OR Apache-2.0
//
//! Provides idiomatic Rust implementations for various Windows string types:
//!
//! * [`NtUnicodeString`] (with [`NtUnicodeStr`] and [`NtUnicodeStrMut`]):
//!   For interfacing with the Windows kernel string type known as [`UNICODE_STRING`]
//! * [`U16StrLe`]:
//!   For working with byte slices of UTF-16 (little-endian) strings
//!
//! Other useful UTF-16 string types are already provided by the excellent [`widestring`] crate.
//! This crate tries to integrate as best as possible with them.
//!
//! [`NtUnicodeStr`]: crate::unicode_string::NtUnicodeStr
//! [`NtUnicodeString`]: crate::unicode_string::NtUnicodeString
//! [`NtUnicodeStrMut`]: crate::unicode_string::NtUnicodeStrMut
//! [`U16StrLe`]: crate::u16strle::U16StrLe
//! [`UNICODE_STRING`]: https://learn.microsoft.com/windows/win32/api/ntdef/ns-ntdef-_unicode_string
//! [`widestring`]: https://crates.io/crates/widestring

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(missing_docs)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub use widestring;

mod error;
pub use error::*;

mod helpers;

mod macros;
pub use macros::*;

pub mod traits;
pub mod u16strle;
pub mod unicode_string;
