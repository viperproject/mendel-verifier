// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::errors::{EncodingError, SpannedEncodingError};
use log::trace;
use prusti_rustc_interface::errors::MultiSpan;

/// Helper trait to add spans to encoding errors.
pub trait WithSpan<T> {
    /// Set the span of the error, overwriting any previous span.
    fn with_span<S: Into<MultiSpan>>(self, span: S) -> Result<T, SpannedEncodingError>;

    /// Like `with_span`, but the span is only computed if an error occurs.
    fn set_span_with<S: Into<MultiSpan>>(
        self,
        span_callback: impl Fn() -> S,
    ) -> Result<T, SpannedEncodingError>;

    /// Set the span of the error, but only if there is no previous span.
    fn with_default_span<S: Into<MultiSpan>>(self, span: S) -> Result<T, SpannedEncodingError>;

    /// Like `with_span`, but the span is only set if it is `Some`.
    fn with_opt_span<S: Into<MultiSpan>>(self, span: Option<S>) -> Result<T, EncodingError>;
}

/// Helper trait to add spans to encoding errors.
pub trait WithOptDefaultSpan<T> {
    /// Like `with_default_span`, but the span is only set if it is `Some`.
    fn with_opt_default_span<S: Into<MultiSpan>>(self, span: Option<S>)
        -> Result<T, EncodingError>;
}

impl<T> WithSpan<T> for Result<T, EncodingError> {
    fn with_span<S: Into<MultiSpan>>(self, span: S) -> Result<T, SpannedEncodingError> {
        self.map_err(|err| {
            trace!("Converting a EncodingError to SpannedEncodingError in a Result");
            err.with_span(span)
        })
    }

    fn set_span_with<S: Into<MultiSpan>>(
        self,
        span_callback: impl Fn() -> S,
    ) -> Result<T, SpannedEncodingError> {
        self.map_err(|err| {
            trace!("Converting a EncodingError to SpannedEncodingError in a Result");
            let span = span_callback();
            err.with_span(span)
        })
    }

    fn with_default_span<S: Into<MultiSpan>>(self, span: S) -> Result<T, SpannedEncodingError> {
        self.map_err(|err| {
            trace!("Converting a EncodingError to SpannedEncodingError in a Result");
            err.with_default_span(span)
        })
    }

    fn with_opt_span<S: Into<MultiSpan>>(self, span: Option<S>) -> Result<T, EncodingError> {
        if let Some(actual_span) = span {
            Ok(self.with_span(actual_span)?)
        } else {
            self
        }
    }
}

impl<T> WithOptDefaultSpan<T> for Result<T, EncodingError> {
    fn with_opt_default_span<S: Into<MultiSpan>>(
        self,
        span: Option<S>,
    ) -> Result<T, EncodingError> {
        if let Some(actual_span) = span {
            Ok(self.with_default_span(actual_span)?)
        } else {
            self
        }
    }
}

impl<T> WithSpan<T> for Result<T, SpannedEncodingError> {
    fn with_span<S: Into<MultiSpan>>(self, span: S) -> Result<T, SpannedEncodingError> {
        self.map_err(|err| {
            trace!("Replacing the span of an SpannedEncodingError in a Result");
            err.with_span(span)
        })
    }

    fn set_span_with<S: Into<MultiSpan>>(
        self,
        span_callback: impl Fn() -> S,
    ) -> Result<T, SpannedEncodingError> {
        self.map_err(|err| {
            trace!("Converting a EncodingError to SpannedEncodingError in a Result");
            let span = span_callback();
            err.with_span(span)
        })
    }

    fn with_default_span<S: Into<MultiSpan>>(self, _span: S) -> Result<T, SpannedEncodingError> {
        trace!("Ignoring the span because the error already has one.");
        self
    }

    fn with_opt_span<S: Into<MultiSpan>>(self, span: Option<S>) -> Result<T, EncodingError> {
        Ok(if let Some(actual_span) = span {
            self.with_span(actual_span)
        } else {
            self
        }?)
    }
}
