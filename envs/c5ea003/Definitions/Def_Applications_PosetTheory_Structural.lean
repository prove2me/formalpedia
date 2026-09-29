-- Prove2me | Definitions.Def_Applications_PosetTheory_Structural
-- name    : Applications_PosetTheory_Structural
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:13.55416+00:00
-- url     : https://prove2.me/theorems/f130e2be-7393-4f85-8b6a-d48f8598e324
-- title:
--   Aether Catalog definitions — Applications_PosetTheory_Structural
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PosetTheory.Structural`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PosetTheory/Structural.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_PosetTheory_MatroidMinorBasic
/-
Copyright (c) 2024 Harmonic Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Structural Results on Matroid Minors

This file develops deeper structural results about matroid minors, including:

1. **Minor-closed class lattice**: The collection of minor-closed properties forms a
   complete lattice under inclusion.
2. **Excluded minor duality**: The excluded minors of a self-dual property are
   closed under duality.
3. **Representability exclusion**: If a matroid has a non-representable minor,
   it is itself non-representable.
4. **WQO product theorem for matroid invariants**: If a matroid invariant takes
   values in a WQO, certain structural consequences follow.

## Main Results

* `minorClosed_inter`: Intersection of minor-closed properties is minor-closed.
* `minorClosed_union_ground`: The property of having ground set contained in a
  fixed set is minor-closed.
* `excluded_minor_dual_of_self_dual`: Self-dual properties have dual-closed excluded minors.
* `not_representable_of_minor_not_representable`: Non-representability propagates upward.
* `minor_ground_card_le`: A minor on a finite ground set has at most as many elements.

## References

* Oxley: "Matroid Theory", Chapter 3 (Minors)
* Geelen, Gerards, Whittle: "Solving Rota's conjecture"
-/

open Set Matroid

noncomputable section

variable {α : Type*}

/-! ## Minor-Closed Property Lattice -/

/-
The intersection of two minor-closed properties is minor-closed.
-/

/-
The union of two minor-closed properties is minor-closed.
-/

/-
The property "ground set is a subset of S" is minor-closed.
-/

/-! ## Excluded Minor Duality -/

/-- A property is **self-dual** if it holds for M iff it holds for M✶. -/
def IsSelfDualProperty (P : Matroid α → Prop) : Prop :=
  ∀ M : Matroid α, P M ↔ P M✶

/-
For a self-dual, minor-closed property, if N is a forbidden minor,
then so is N✶. This means the set of excluded minors is closed under duality.
-/

/-! ## Representability and Minor Monotonicity -/

/-
If a matroid has a minor that is not F-representable,
then the matroid itself cannot be F-representable (contrapositive of
representability being minor-closed for deletion).
-/

/-! ## Ground Set Cardinality -/

/-
A minor of a matroid with finite ground set has a ground set of
at most the same cardinality.
-/

/-! ## Matroid Invariants Under Minors -/

-- placeholder for isomorphism invariance



/-! ## Minor-Closed Classes and Finite Characterization -/




end


