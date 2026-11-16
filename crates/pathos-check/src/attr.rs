//! Attributes of symbols (`attr.h` and `expr_info.h` in Ethos).

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use std::fmt;

use pathos_term::{Kind, Term};

/// An attribute. Those from `List` on say how applications of a symbol are
/// built, or what the symbol is; a symbol has at most one of them.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::external_derive)]
pub enum Attr {
    #[default]
    None,
    Implicit,
    Type,
    IsEq,
    Sorry,
    List,
    Program,
    Binder,
    LetBinder,
    Opaque,
    Syntax,
    Restrict,
    /// A proof rule. Its term is the tuple (premise-list operator or `eo::?`,
    /// takes an assumption, conclusion is explicit, program or conclusion).
    ProofRule,
    RightAssoc,
    LeftAssoc,
    RightAssocNil,
    LeftAssocNil,
    RightAssocNsNil,
    LeftAssocNsNil,
    Chainable,
    Pairwise,
    ArgList,
    /// A function whose applications need a type annotation, e.g. `set.empty`.
    Amb,
    Datatype,
    DatatypeConstructor,
    AmbDatatypeConstructor,
}

// `==` on attributes is the derived one, which Verus cannot look into; see
// the same for the kinds in `pathos-term`.
#[cfg(verus_keep_ghost)]
verus! {

impl vstd::std_specs::cmp::PartialEqSpecImpl for Attr {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Attr) -> bool {
        *self == *other
    }
}

impl Attr {
    /// See [`Attr::is_list_nil`].
    pub open spec fn spec_is_list_nil(self) -> bool {
        matches!(self, Attr::LeftAssocNil | Attr::RightAssocNil | Attr::RightAssocNsNil | Attr::LeftAssocNsNil)
    }

    /// See [`Attr::is_left_nil`].
    pub open spec fn spec_is_left_nil(self) -> bool {
        matches!(self, Attr::LeftAssocNil | Attr::LeftAssocNsNil)
    }
}

} // verus!

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Attr {
    /// Whether a symbol with this attribute takes any number of arguments.
    pub fn is_nary(self) -> bool {
        matches!(
            self,
            Attr::LeftAssoc
                | Attr::RightAssoc
                | Attr::LeftAssocNil
                | Attr::RightAssocNil
                | Attr::RightAssocNsNil
                | Attr::LeftAssocNsNil
                | Attr::Chainable
                | Attr::Pairwise
                | Attr::ArgList
        )
    }

    /// Whether this is one of the associative attributes with a nil
    /// terminator.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == self.spec_is_list_nil(),))]
    pub fn is_list_nil(self) -> bool {
        matches!(
            self,
            Attr::LeftAssocNil | Attr::RightAssocNil | Attr::RightAssocNsNil | Attr::LeftAssocNsNil
        )
    }

    /// Whether this is left associative with a nil terminator.
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == self.spec_is_left_nil(),))]
    pub fn is_left_nil(self) -> bool {
        matches!(self, Attr::LeftAssocNil | Attr::LeftAssocNsNil)
    }

    /// Whether the attribute says how to build applications.
    pub fn is_constructor_kind(self) -> bool {
        self.is_nary() || matches!(self, Attr::Binder | Attr::LetBinder | Attr::List)
    }
}

impl fmt::Display for Attr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Attr::None => "NONE",
            Attr::Implicit => "implicit",
            Attr::Type => "type",
            Attr::IsEq => "is_eq",
            Attr::Sorry => "sorry",
            Attr::List => "list",
            Attr::ProofRule => "proof_rule",
            Attr::Program => "program",
            Attr::Binder => "binder",
            Attr::LetBinder => "let_binder",
            Attr::Opaque => "opaque",
            Attr::Syntax => "syntax",
            Attr::Restrict => "restrict",
            Attr::RightAssoc => "right-assoc",
            Attr::LeftAssoc => "left-assoc",
            Attr::RightAssocNil => "right-assoc-nil",
            Attr::LeftAssocNil => "left-assoc-nil",
            Attr::RightAssocNsNil => "right-assoc-non-singleton-nil",
            Attr::LeftAssocNsNil => "left-assoc-non-singleton-nil",
            Attr::Chainable => "chainable",
            Attr::Pairwise => "pairwise",
            Attr::ArgList => "arg-list",
            Attr::Datatype => "datatype",
            Attr::Amb => "amb",
            Attr::DatatypeConstructor => "datatype_constructor",
            Attr::AmbDatatypeConstructor => "amb_datatype_constructor",
        })
    }
}

/// What the checker knows about a symbol beyond its type: how to build its
/// applications.
#[derive(Clone, Default, Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify, verifier::external_derive)]
pub struct AppInfo {
    /// The symbol's constructor attribute.
    pub attr: Attr,
    /// The term that goes with the attribute, e.g. the nil terminator.
    pub cons: Option<Term>,
    /// For builtin symbols such as `->` and `eo::add`: the kind of term an
    /// application of the symbol builds.
    pub kind: Option<Kind>,
    /// Whether the symbol's name is bound to more than one term. The terms
    /// are then listed under `overload_name` in the checker.
    pub overloaded: bool,
    pub overload_name: String,
}
