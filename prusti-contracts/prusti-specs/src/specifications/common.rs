//! Data structures for storing information about specifications.
//!
//! Please see the `parser.rs` file for more information about
//! specifications.

use std::{
    convert::TryFrom,
    fmt::{Debug, Display},
};
use uuid::Uuid;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// A specification type.
pub enum SpecType {
    /// Precondition of a procedure.
    Precondition,
    /// Postcondition of a procedure.
    Postcondition,
    /// Loop invariant
    Invariant,
    /// Predicate
    Predicate,
    /// Struct invariant
    StructInvariant,
}

#[derive(Debug)]
/// A conversion from string into specification type error.
pub enum TryFromStringError {
    /// Reported when the string being converted is not one of the
    /// following: `requires`, `ensures`, `invariant`.
    UnknownSpecificationType,
}

impl<'a> TryFrom<&'a str> for SpecType {
    type Error = TryFromStringError;

    fn try_from(typ: &str) -> Result<SpecType, TryFromStringError> {
        match typ {
            "requires" => Ok(SpecType::Precondition),
            "ensures" => Ok(SpecType::Postcondition),
            "invariant" => Ok(SpecType::Invariant),
            "predicate" => Ok(SpecType::Predicate),
            _ => Err(TryFromStringError::UnknownSpecificationType),
        }
    }
}

#[derive(
    Debug,
    Default,
    PartialEq,
    Eq,
    Hash,
    Clone,
    Copy,
    serde::Serialize,
    serde::Deserialize,
    PartialOrd,
    Ord,
)]
/// A unique ID of the specification element such as entire precondition
/// or postcondition.
pub struct SpecificationId(Uuid);

/// A reference to a procedure specification.
#[derive(Debug, Clone, Copy)]
pub enum SpecIdRef {
    Precondition(SpecificationId),
    Postcondition(SpecificationId),
    Purity(SpecificationId),
    Pledge {
        lhs: Option<SpecificationId>,
        rhs: SpecificationId,
    },
    Predicate(SpecificationId),
    Terminates(SpecificationId),
}

impl Display for SpecificationId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0.simple().encode_lower(&mut Uuid::encode_buffer()),
        )
    }
}

impl std::convert::TryFrom<String> for SpecificationId {
    type Error = uuid::Error;
    fn try_from(value: String) -> Result<Self, Self::Error> {
        Uuid::parse_str(&value).map(Self)
    }
}

impl SpecificationId {
    pub fn dummy() -> Self {
        Self(Uuid::nil())
    }
}

pub(crate) struct SpecificationIdGenerator {}

impl SpecificationIdGenerator {
    pub(crate) fn new() -> Self {
        Self {}
    }
    pub(crate) fn generate(&mut self) -> SpecificationId {
        SpecificationId(Uuid::new_v4())
    }
}

pub(crate) fn generate_struct_name(item: &syn::ItemImpl) -> String {
    let uuid = Uuid::new_v4().simple();
    let name_ty = generate_name_for_type(&item.self_ty).unwrap_or_default();
    format!("PrustiStruct{name_ty}_{uuid}")
}

pub(crate) fn generate_struct_name_for_trait(item: &syn::ItemTrait) -> String {
    let uuid = Uuid::new_v4().simple();
    format!("PrustiTrait{}_{}", item.ident, uuid)
}

fn generate_name_for_type(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Path(ty_path) => Some(String::from_iter(
            ty_path
                .path
                .segments
                .iter()
                .map(|seg| seg.ident.to_string()),
        )),
        syn::Type::Slice(ty_slice) => {
            let ty = &*ty_slice.elem;
            Some(format!("Slice{}", generate_name_for_type(ty)?.as_str()))
        }
        _ => None,
    }
}

/// Ownership kind, used to specify library ownership.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OwnershipKind {
    WriteRef,
    LocalRef,
    ReadRef,
    Unique,
    Local,
    Immutable,
    Read,
    Write,
    NoReadRef,
    NoWriteRef,
}

impl TryFrom<&str> for OwnershipKind {
    type Error = ();

    fn try_from(typ: &str) -> Result<OwnershipKind, ()> {
        match typ {
            "readRef" => Ok(OwnershipKind::ReadRef),
            "localRef" => Ok(OwnershipKind::LocalRef),
            "writeRef" => Ok(OwnershipKind::WriteRef),
            "unique" => Ok(OwnershipKind::Unique),
            "local" => Ok(OwnershipKind::Local),
            "immutable" => Ok(OwnershipKind::Immutable),
            "read" => Ok(OwnershipKind::Read),
            "write" => Ok(OwnershipKind::Write),
            "noReadRef" => Ok(OwnershipKind::NoReadRef),
            "noWriteRef" => Ok(OwnershipKind::NoWriteRef),
            _ => Err(()),
        }
    }
}

impl Display for OwnershipKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OwnershipKind::ReadRef => write!(f, "readRef"),
            OwnershipKind::LocalRef => write!(f, "localRef"),
            OwnershipKind::WriteRef => write!(f, "writeRef"),
            OwnershipKind::Unique => write!(f, "unique"),
            OwnershipKind::Local => write!(f, "local"),
            OwnershipKind::Immutable => write!(f, "immutable"),
            OwnershipKind::Read => write!(f, "read"),
            OwnershipKind::Write => write!(f, "write"),
            OwnershipKind::NoReadRef => write!(f, "noReadRef"),
            OwnershipKind::NoWriteRef => write!(f, "noWriteRef"),
        }
    }
}
