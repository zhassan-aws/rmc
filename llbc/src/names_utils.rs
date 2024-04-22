//! Defines some utilities for [crate::names]
//!
//! For now, we have one function per object kind (type, trait, function,
//! module): many of them could be factorized (will do).
use crate::formatter::AstFormatter;
use crate::names::*;
use crate::types::*;
use std::collections::HashSet;

impl PathElem {
    fn equals_ident(&self, id: &str) -> bool {
        match self {
            PathElem::Ident(s, d) => s == id && d.is_zero(),
            PathElem::Impl(_) => false,
        }
    }

    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        match self {
            PathElem::Ident(s, d) => {
                let d = if d.is_zero() { "".to_string() } else { format!("#{}", d) };
                format!("{s}{d}")
            }
            PathElem::Impl(impl_elem) => impl_elem.fmt_with_ctx(ctx),
        }
    }
}

impl ImplElemKind {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        match self {
            ImplElemKind::Ty(ty) => ty.fmt_with_ctx(ctx),
            ImplElemKind::Trait(tr) => {
                // We need to put the first type parameter aside: it is
                // the type for which we implement the trait.
                // This is not very clean because it's hard to move the
                // first element out of a vector...
                let TraitDeclRef { trait_id, generics } = tr;
                let (ty, generics) = generics.pop_first_type_arg();
                let tr = TraitDeclRef { trait_id: *trait_id, generics };
                format!("impl {} for {}", tr.fmt_with_ctx(ctx), ty.fmt_with_ctx(ctx))
            }
        }
    }
}

impl ImplElem {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        let d = if self.disambiguator.is_zero() {
            "".to_string()
        } else {
            format!("#{}", self.disambiguator)
        };
        let ctx = ctx.set_generics(&self.generics);
        // Just printing the generics (not the predicates)
        format!("{{{}{d}}}", self.kind.fmt_with_ctx(&ctx),)
    }
}

impl Name {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        let name = self.name.iter().map(|x| x.fmt_with_ctx(ctx)).collect::<Vec<String>>();
        name.join("::")
    }
}

impl Name {
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.name.len()
    }

    /// Compare the name to a constant array.
    /// This ignores disambiguators.
    ///
    /// `equal`: if `true`, check that the name is equal to the ref. If `false`:
    /// only check if the ref is a prefix of the name.
    pub fn compare_with_ref_name(&self, equal: bool, ref_name: &[&str]) -> bool {
        let name: Vec<&PathElem> = self.name.iter().filter(|e| e.is_ident()).collect();

        if name.len() < ref_name.len() || (equal && name.len() != ref_name.len()) {
            return false;
        }

        for i in 0..ref_name.len() {
            if !name[i].equals_ident(ref_name[i]) {
                return false;
            }
        }
        true
    }

    /// Compare the name to a constant array.
    /// This ignores disambiguators.
    pub fn equals_ref_name(&self, ref_name: &[&str]) -> bool {
        self.compare_with_ref_name(true, ref_name)
    }

    /// Compare the name to a constant array.
    /// This ignores disambiguators.
    pub fn prefix_is_same(&self, ref_name: &[&str]) -> bool {
        self.compare_with_ref_name(false, ref_name)
    }

    /// Return `true` if the name identifies an item inside the module: `krate::module`
    pub fn is_in_module(&self, krate: &String, module: &String) -> bool {
        self.prefix_is_same(&[krate, module])
    }

    /// Similar to [Name::is_in_module]
    pub fn is_in_modules(&self, krate: &String, modules: &HashSet<String>) -> bool {
        if self.len() >= 2 {
            match (&self.name[0], &self.name[1]) {
                (PathElem::Ident(s0, _), PathElem::Ident(s1, _)) => {
                    s0 == krate && modules.contains(s1)
                }
                _ => false,
            }
        } else {
            false
        }
    }
}
