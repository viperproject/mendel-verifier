// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub use prusti_rustc_interface::{
    hir, hir::def_id::{DefId, LOCAL_CRATE}, middle::{ty, mir}, target::abi,
    data_structures::fx::{FxHashMap, FxHashSet},
    errors::MultiSpan,
    span::Span,
    middle::mir::tcx::PlaceTy,
};
pub use vir_crate::polymorphic as vir;
pub use vir_crate::polymorphic::ExprIterator;
pub use crate::{error_internal, error_incorrect, error_unsupported, open_trace, close_trace};
pub use crate::encoder::{
    Encoder,
    errors::{
        EncodingResult, SpannedEncodingResult, EncodingError, SpannedEncodingError,
        ErrorCtxt, WithSpan, WithOptDefaultSpan,
    },
    builtin_encoder::{BuiltinDomainKind, BuiltinMethodKind, BuiltinFunctionKind},
    safe_clients::{
        *,
        address_domain::AddressDomain,
        ownership_domain::{OwnershipKind, OwnershipDomain},
        snapshot_domains::mem_snapshot_domain::MemSnapshotDomain,
        snapshot_domains::value_snapshot_domain::ValueSnapshotDomain,
        encoding_traits::*,
        encoding_structs::*,
        snapshot_domains::*,
    }
};
pub use log::{trace, debug, info, warn, error};
pub use prusti_common::{config, vir_type, vir_local, vir_expr, vir_stmt};
pub use prusti_interface::environment::{Environment, body::MirBody};
