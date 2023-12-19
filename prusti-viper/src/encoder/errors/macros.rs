// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#[macro_export]
macro_rules! build_error_internal {
    ($span:expr => $($message:tt)+) => {
        $crate::encoder::errors::SpannedEncodingError::internal(format!($($message)+), $span)
    };
    ($($message:tt)+) => {
        $crate::encoder::errors::EncodingError::internal(format!($($message)+))
    };
}

#[macro_export]
macro_rules! build_error_incorrect {
    ($span:expr => $($message:tt)+) => {
        $crate::encoder::errors::SpannedEncodingError::incorrect(format!($($message)+), $span)
    };
    ($($message:tt)+) => {
        $crate::encoder::errors::EncodingError::incorrect(format!($($message)+))
    };
}

#[macro_export]
macro_rules! build_error_unsupported {
    ($span:expr => $($message:tt)+) => {
        $crate::encoder::errors::SpannedEncodingError::unsupported(format!($($message)+), $span)
    };
    ($($message:tt)+) => {
        $crate::encoder::errors::EncodingError::unsupported(format!($($message)+))
    };
}

#[macro_export]
macro_rules! error_internal {
    (opt $span:expr => $($message:tt)+) => {
        if let Some(actual_span) = $span {
            return Err($crate::encoder::errors::EncodingError::from(
                $crate::build_error_internal!(actual_span => $($message)+)
            ))
        } else {
            return Err($crate::build_error_internal!($($message)+))
        }
    };
    ($($message:tt)+) => {
        return Err($crate::build_error_internal!($($message)+))
    };
}

#[macro_export]
macro_rules! error_incorrect {
    (opt $span:expr => $($message:tt)+) => {
        if let Some(actual_span) = $span {
            return Err($crate::encoder::errors::EncodingError::from(
                $crate::build_error_incorrect!(actual_span => $($message)+)
            ))
        } else {
            return Err($crate::build_error_incorrect!($($message)+))
        }
    };
    ($($message:tt)+) => {
        return Err($crate::build_error_incorrect!($($message)+))
    };
}

#[macro_export]
macro_rules! error_unsupported {
    (opt $span:expr => $($message:tt)+) => {
        if let Some(actual_span) = $span {
            return Err($crate::encoder::errors::EncodingError::from(
                $crate::build_error_unsupported!(actual_span => $($message)+)
            ))
        } else {
            return Err($crate::build_error_unsupported!($($message)+))
        }
    };
    ($($message:tt)+) => {
        return Err($crate::build_error_unsupported!($($message)+))
    };
}
