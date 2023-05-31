// Copyright 2023 Colin Finck <colin@reactos.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use displaydoc::Display;

/// Central result type of nt-string.
pub type Result<T, E = NtStringError> = core::result::Result<T, E>;

/// Central error type of nt-string.
#[derive(Clone, Debug, Display, Eq, PartialEq)]
#[non_exhaustive]
pub enum NtStringError {
    /// The required buffer size exceeds an unsigned 16-bit integer (65535 bytes).
    BufferSizeExceedsU16,
    /// No NUL character could be found.
    NulNotFound,
    /// The buffer could not be decoded as UTF-16 due to the unpaired surrogate {unpaired_surrogate:#06X}.
    UnpairedUtf16Surrogate {
        /// Numeric value of the unpaired surrogate
        unpaired_surrogate: u16,
    },
}

impl From<widestring::error::DecodeUtf16Error> for NtStringError {
    fn from(e: widestring::error::DecodeUtf16Error) -> Self {
        Self::UnpairedUtf16Surrogate {
            unpaired_surrogate: e.unpaired_surrogate(),
        }
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl std::error::Error for NtStringError {}
