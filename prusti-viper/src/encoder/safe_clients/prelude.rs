// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub use crate::{
    close_trace,
    encoder::{
        builtin_encoder::{BuiltinDomainKind, BuiltinFunctionKind, BuiltinMethodKind},
        errors::{
            EncodingError, EncodingResult, ErrorCtxt, SpannedEncodingError, SpannedEncodingResult,
            WithOptDefaultSpan, WithSpan,
        },
        safe_clients::{
            address_domain::AddressDomain,
            encoding_structs::*,
            encoding_traits::*,
            ownership_domain::{OwnershipDomain, OwnershipKind},
            snapshot_domains::{
                mem_snapshot_domain::MemSnapshotDomain, value_snapshot_domain::ValueSnapshotDomain,
                *,
            },
            *,
        },
        Encoder,
    },
    error_incorrect, error_internal, error_unsupported, open_trace,
};
pub use log::{debug, error, info, trace, warn};
pub use prusti_common::{config, vir_expr, vir_local, vir_stmt, vir_type};
pub use prusti_interface::environment::{body::MirBody, Environment};
pub use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    errors::MultiSpan,
    hir,
    hir::def_id::{DefId, LOCAL_CRATE},
    middle::{mir, mir::tcx::PlaceTy, ty},
    span::Span,
    target::abi,
};
pub use vir_crate::{polymorphic as vir, polymorphic::ExprIterator};
