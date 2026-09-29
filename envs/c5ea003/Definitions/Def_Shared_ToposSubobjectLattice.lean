-- Prove2me | Definitions.Def_Shared_ToposSubobjectLattice
-- name    : Shared_ToposSubobjectLattice
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:15:12.431141+00:00
-- url     : https://prove2.me/theorems/4530affa-b4e6-4cd0-b257-c7dc8c42f155
-- title:
--   Aether Catalog definitions — Shared_ToposSubobjectLattice
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ToposSubobjectLattice`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ToposSubobjectLattice.lean by skeleton subtraction
import Mathlib

/-! # The bounded lattice universal property attached to a Grothendieck topos

A Grothendieck topos is a category, not a lattice, so the literal assertion that
"every Grothendieck topos is a bounded lattice" is ill-typed.  The standard true
statement is that the subobjects of each object form a complete Heyting algebra
(a frame).  This file formalizes the algebraic universal property shared by all
such subobject frames and gives the frame of open sets as its concrete sheaf-topos
model.

The central universal property says that Heyting implication `a ⇨ c` is the
greatest `x` for which `a ⊓ x ≤ c`; equivalently, meet with `a` is left adjoint
to implication by `a`.
-/

namespace ToposSubobjectLattice

universe u

variable {L : Type u} [Order.Frame L]





/-- Double negation on the intuitionistic subobject frame. -/
def doubleNegation (a : L) : L := aᶜᶜ







/-- A regular subobject is one fixed by double negation. -/
def IsRegular (a : L) : Prop := doubleNegation a = a


section Opens

variable {X : Type u} [TopologicalSpace X]



end Opens

end ToposSubobjectLattice


