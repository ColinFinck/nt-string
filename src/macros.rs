// Copyright 2023 Colin Finck <colin@reactos.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

// #[macro_export] always exports all macros at the root, even when they better fit to individual modules.
// This is a current limitation of the Rust macro system.
//
// As a consequence, I'm also grouping all public macros here instead of giving people a wrong idea
// by associating them to modules.

/// Creates an [`NtUnicodeStr`] with `'static` lifetime for a string literal.
///
/// The internal buffer of the [`NtUnicodeStr`] will consist entirely of valid UTF-16 characters.
///
/// The internal buffer will also be NUL-terminated.
/// See the [unicode_string module-level documentation](crate::unicode_string) for the implications of that.
///
/// [`NtUnicodeStr`]: crate::unicode_string::NtUnicodeStr
#[macro_export]
macro_rules! nt_unicode_str {
    ($text:expr) => {{
        const U16CSTR: &'static $crate::widestring::U16CStr = $crate::widestring::u16cstr!($text);

        let buffer = U16CSTR.as_slice_with_nul();

        // Include the terminating NUL character in `maximum_length` ...
        let maximum_length_in_elements = buffer.len();
        let maximum_length_in_bytes = maximum_length_in_elements * ::core::mem::size_of::<u16>();

        assert!(
            maximum_length_in_bytes <= ::core::primitive::u16::MAX as usize,
            "String is too long (resulting byte length exceeds a u16)"
        );

        let maximum_length = maximum_length_in_bytes as u16;

        // ... but not in `length`
        assert!(maximum_length >= ::core::mem::size_of::<u16>() as u16);
        let length = maximum_length - ::core::mem::size_of::<u16>() as u16;

        unsafe {
            $crate::unicode_string::NtUnicodeStr::from_raw_parts(
                buffer.as_ptr(),
                length,
                maximum_length,
            )
        }
    }};
}

#[cfg(test)]
mod tests {
    use crate::unicode_string::NtUnicodeStr;

    const TEST_STR: NtUnicodeStr<'static> = nt_unicode_str!("Moin");

    #[test]
    fn test_nt_unicode_str() {
        assert_eq!(TEST_STR, "Moin");
        assert_eq!(TEST_STR.len(), 8);
        assert_eq!(TEST_STR.capacity(), 10);
    }
}
