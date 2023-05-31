// Copyright 2023 Colin Finck <colin@reactos.org>
// SPDX-License-Identifier: MIT OR Apache-2.0
//
//! Additional traits provided by this crate.

/// Fallible variant of the [`Extend`] trait
pub trait TryExtend<T> {
    /// The type returned in the event of an error.
    type Error;

    /// Tries to extends a collection with the contents of an iterator.
    fn try_extend<I: IntoIterator<Item = T>>(&mut self, iter: I) -> Result<(), Self::Error>;

    /// Tries to extend a collection with exactly one element.
    fn try_extend_one(&mut self, item: T) -> Result<(), Self::Error> {
        self.try_extend(Some(item))
    }
}
