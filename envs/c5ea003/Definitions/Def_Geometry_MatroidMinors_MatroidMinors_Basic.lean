-- Prove2me | Definitions.Def_Geometry_MatroidMinors_MatroidMinors_Basic
-- name    : Geometry_MatroidMinors_MatroidMinors_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:43:59.982729+00:00
-- url     : https://prove2.me/theorems/9adb4e76-8f25-4cdf-83ee-132ec6bb109a
-- title:
--   Aether Catalog definitions — Geometry_MatroidMinors_MatroidMinors_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.MatroidMinors.MatroidMinors.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/MatroidMinors/MatroidMinors_Basic.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2024 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Matroid Minors and the Robertson-Seymour Conjecture for Representable Matroids

This file develops the theory of matroid minors, minor-closed properties, and their
characterization by forbidden minors. We formalize:

1. **Minor-closed predicates** and the notion of excluded minors
2. **The dual-minor correspondence**: duality commutes with the minor relation
3. **WQO implies finite forbidden minor characterization**: the key structural theorem
4. **Antichain finiteness** from well-quasi-ordering

## Main Results

* `MatroidMinor.dual_isMinor_dual` — if N ≤m M then N✶ ≤m M✶
* `MatroidMinor.excluded_minors_antichain` — excluded minors form an antichain
* `MatroidMinor.wqo_implies_finite_antichains` — WQO implies all antichains are finite
* `MatroidMinor.dual_minor_closed` — duality preserves minor-closure

## References

* Robertson, N. and Seymour, P.D., "Graph Minors. XX. Wagner's conjecture", JCTB 2004
* Geelen, J., Gerards, B., Whittle, G., "Solving Rota's Conjecture", Notices AMS 2014
-/

open Set Matroid

noncomputable section

namespace MatroidMinor

variable {α : Type*}

/-! ## Minor-Closed Predicates -/

/-- A predicate on matroids is **minor-closed** if whenever `M` satisfies the predicate
and `N` is a minor of `M`, then `N` also satisfies the predicate. -/
def IsMinorClosed (P : Matroid α → Prop) : Prop :=
  ∀ ⦃M N : Matroid α⦄, P M → N ≤m M → P N

/-- An **excluded minor** for a minor-closed property `P` is a matroid that does not
satisfy `P`, but every proper minor does satisfy `P`. -/
def IsExcludedMinor (P : Matroid α → Prop) (M : Matroid α) : Prop :=
  ¬ P M ∧ ∀ ⦃N : Matroid α⦄, N <m M → P N

/-! ## Dual-Minor Correspondence -/

/-
**Dual-Minor Theorem**: If `N` is a minor of `M`, then `N✶` is a minor of `M✶`.
This is a fundamental result in matroid theory showing that duality commutes with
the minor relation.

The proof uses the fact that `(M ／ C ＼ D)✶ = M✶ ＼ C ／ D`, so if `N = M ／ C ＼ D`,
then `N✶ = M✶ ＼ C ／ D`, which is also a minor of `M✶` (obtained by deleting `C`
then contracting `D`).
-/

/-
Taking duals preserves the minor relation in both directions: `N✶ ≤m M✶ ↔ N ≤m M`.
-/

/-! ## Antichain Theory -/

/-- An **antichain** in the minor order is a set of matroids where no one is a proper
minor of any other. -/
def IsMinorAntichain (S : Set (Matroid α)) : Prop :=
  ∀ M ∈ S, ∀ N ∈ S, M ≤m N → M = N

/-
The set of excluded minors for a minor-closed property forms an antichain
in the minor order. If two excluded minors were comparable (one a minor of the other),
the smaller one would satisfy the property (by the excluded minor condition on the larger),
contradicting it being an excluded minor.
-/

/-! ## Well-Quasi-Ordering and Finite Antichains -/

/-- A class of matroids is **well-quasi-ordered** by the minor relation if every infinite
sequence contains a pair where one is a minor of the other. -/
def IsMinorWQO (S : Set (Matroid α)) : Prop :=
  ∀ (f : ℕ → Matroid α), (∀ n, f n ∈ S) →
    ∃ i j, i < j ∧ f i ≤m f j

/-
**Key Structural Theorem**: In a well-quasi-ordered class, every antichain is finite.
This is the fundamental fact that connects WQO to the finite forbidden minor property.

The proof is by contraposition: if an antichain were infinite, we could extract an
infinite sequence of distinct elements, violating the WQO property.
-/


/-! ## Minor-Closed Property of Duality -/

/-
If `P` is minor-closed, then so is the dual property `fun M => P M✶`.
-/

/-! ## Ground Set Properties -/

/-
A strict minor has a strictly smaller ground set (for finite matroids).
-/

end MatroidMinor

end


