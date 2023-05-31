// Copyright 2023 Colin Finck <colin@reactos.org>
// SPDX-License-Identifier: MIT OR Apache-2.0
//
//! Interface around the Windows kernel string type known as [`UNICODE_STRING`].
//!
//! The [`UNICODE_STRING`] type was designed for the C programming language, which only knows about NUL-terminated
//! buffers of characters.
//! To determine the length of such a buffer, you need to iterate over all characters until finding the NUL.
//! Bad enough?
//! It gets worse:
//! A classic buffer overflow occurs if the buffer contains no NUL, but an algorithm attempts to find
//! it anyway.
//!
//! To overcome these performance and security hazards, [`UNICODE_STRING`]s consist of a buffer, a buffer capacity
//! ("maximum length"), and a field to indicate the actually used length.
//! Determining length and capacity is now as simple as querying the corresponding fields.
//!
//! Length and capacity are 16-bit values and expressed in bytes.
//! This allows for up to 32767 UTF-16 characters per string.
//! However, note that additional space may be occupied by a NUL terminator or by UTF-16 characters outside the
//! [Basic Multilingual Plane] (which require 4 bytes per character instead of 2).
//!
//! 32767 characters are way below the expected limit of most data structures.
//! Therefore, most functions of this crate are fallible and may return [`NtStringError::BufferSizeExceedsU16`].
//!
//! While the string length is fully expressed by the `length` field of a [`UNICODE_STRING`] and a NUL termination
//! is not required by the specification, this crate tries to NUL-terminate the internal buffer whenever possible.
//! This defense-in-depth approach guards against external applications that mistakenly treat the internal buffer
//! of a [`UNICODE_STRING`] as a NUL-terminated string.
//! Only a few functions of this crate don't NUL-terminate the internal buffer; they are marked as such.
//!
//! [`UNICODE_STRING`] is implemented in 3 Rust structs:
//!
//! * [`NtUnicodeStr`] is an immutable reference to an existing [`UNICODE_STRING`] in memory
//!   (analogous to `&str`).  
//!   You can also create a constant [`NtUnicodeStr`] using the [`nt_unicode_str`] macro
//!   (analogous to `const STR: &'static str = "..."`).
//!
//! * [`NtUnicodeStrMut`] is a mutable reference to an existing [`UNICODE_STRING`] in memory
//!   (analogous to `&mut str`).  
//!   As it doesn't know how its internal buffer has been allocated, you can only do limited alterations
//!   (like removing a character), but not grow it beyond the buffer size.
//!
//! * [`NtUnicodeString`] is an owned and growable [`UNICODE_STRING`] (analogous to [`String`]).  
//!   It can reallocate the internal buffer on demand and therefore implements all kinds of methods to alter
//!   its contents.
//!
//! [`Deref`] and [`DerefMut`] traits have been implemented to make every [`NtUnicodeString`] act as
//! [`NtUnicodeStrMut`] and every [`NtUnicodeStrMut`] act as [`NtUnicodeStr`] if required.
//!
//! # Examples
//!
//! You can work with these string types just like you work with other Rust string types:
//!
//! ```
//! # use nt_string::unicode_string::NtUnicodeString;
//! let mut string = NtUnicodeString::try_from("Hello! ").unwrap();
//! string.try_push_str("Moin!").unwrap();
//! println!("{string}");
//! ```
//!
//! Conversions are also supported from raw [`u16`] string buffers as well as the [`U16CStr`] and [`U16Str`]
//! types of the [`widestring`] crate:
//!
//! ```
//! # use nt_string::unicode_string::NtUnicodeString;
//! # use widestring::{u16cstr, u16str};
//! let abc = NtUnicodeString::try_from_u16(&[b'A' as u16, b'B' as u16, b'C' as u16]).unwrap();
//! let de = NtUnicodeString::try_from_u16_until_nul(&[b'D' as u16, b'E' as u16, 0]).unwrap();
//! let fgh = NtUnicodeString::try_from(u16cstr!("FGH")).unwrap();
//! let ijk = NtUnicodeString::try_from(u16str!("IJK")).unwrap();
//! ```
//!
//! Just like a [`String`] automatically dereferences to a `&str` when you pass it to an appropriate function,
//! you can do the same with an [`NtUnicodeString`] and it will dereference to an `&NtUnicodeStr`:
//!
//! ```
//! # use nt_string::unicode_string::{NtUnicodeStr, NtUnicodeString};
//! let string = NtUnicodeString::try_from("My String").unwrap();
//! subfunction(&string);
//!
//! fn subfunction(str_ref: &NtUnicodeStr) {
//!     println!("Hello from subfunction with \"{str_ref}\".");
//! }
//! ```
//!
//! Constant [`UNICODE_STRING`]s can be created at compile-time.
//! This provides strings with a `'static` lifetime and saves a UTF-16 conversion at runtime:
//!
//! ```
//! # use nt_string::nt_unicode_str;
//! # use nt_string::unicode_string::NtUnicodeStr;
//! const MY_CONSTANT_STRING: NtUnicodeStr<'static> = nt_unicode_str!("My Constant String");
//! ```
//!
//! Finally, you most likely want to pass your [`NtUnicodeStr`], [`NtUnicodeStrMut`] or [`NtUnicodeString`]
//! to an FFI function that expects a pointer to a [`UNICODE_STRING`].
//! Use the [`as_ptr`] or [`as_mut_ptr`] methods to get an immutable or mutable pointer.
//!
//! [`as_mut_ptr`]: crate::unicode_string::NtUnicodeStrMut::as_mut_ptr
//! [`as_ptr`]: crate::unicode_string::NtUnicodeStr::as_ptr
//! [Basic Multilingual Plane]: https://en.wikipedia.org/wiki/Basic_Multilingual_Plane
//! [`Deref`]: core::ops::Deref
//! [`DerefMut`]: core::ops::DerefMut
//! [`nt_unicode_str`]: crate::nt_unicode_str
//! [`NtStringError::BufferSizeExceedsU16`]: crate::error::NtStringError::BufferSizeExceedsU16
//! [`U16CStr`]: widestring::U16CStr
//! [`U16Str`]: widestring::U16Str
//! [`UNICODE_STRING`]: https://learn.microsoft.com/windows/win32/api/ntdef/ns-ntdef-_unicode_string

pub mod iter;

mod str;
pub use self::str::*;

mod strmut;
pub use self::strmut::*;

#[cfg(feature = "alloc")]
mod string;
#[cfg(feature = "alloc")]
pub use self::string::*;

macro_rules! impl_eq {
    ($lhs:ty, $rhs:ty) => {
        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            fn eq(&self, other: &$lhs) -> bool {
                PartialEq::eq(self.deref(), other.deref())
            }
        }
    };
}
use impl_eq;

macro_rules! impl_partial_cmp {
    ($lhs:ty, $rhs:ty) => {
        impl<'a, 'b> PartialOrd<$lhs> for $rhs {
            fn partial_cmp(&self, other: &$lhs) -> Option<Ordering> {
                PartialOrd::partial_cmp(self.deref(), other.deref())
            }
        }
    };
}
use impl_partial_cmp;
