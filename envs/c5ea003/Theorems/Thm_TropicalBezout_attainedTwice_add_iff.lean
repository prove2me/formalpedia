-- Prove2me | Theorems.Thm_TropicalBezout_attainedTwice_add_iff
-- name    : TropicalBezout.attainedTwice_add_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:20:05.559638+00:00
-- url     : https://prove2.me/theorems/c65c8f79-7a85-45f9-a35a-c4e18d153207
-- title:
--   AttainedTwice add iff
-- statement:
--   Formal statement of `TropicalBezout.attainedTwice_add_iff` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalBezout.attainedTwice_add_iff{ι κ : Type*}
--       [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
--       (a : ι → ℝ) (b : κ → ℝ) :
--       AttainedAtLeastTwice (fun p : ι × κ => a p.1 + b p.2)
--         ↔ AttainedAtLeastTwice a ∨ AttainedAtLeastTwice b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlgebraTropicalGeometry/TropicalBezoutFactorization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlgebraTropicalGeometry/TropicalBezoutFactorization.lean#L113

-- Thm stub generated from Bridges/AlgebraTropicalGeometry/TropicalBezoutFactorization.lean
import Mathlib
import Definitions.Def_Bridges_AlgebraTropicalGeometry_TropicalBezoutFactorization
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Bézout: factorization of tropical hypersurfaces and Newton polytopes

This file *extends* `Bridges.AlgebraTropicalGeometry.TropicalValuationLimitBridge`.  That file
established the bridge between a non-Archimedean valuation and tropical geometry, proving:

* `TropicalValuationBridge.kapranov_easy_direction` — the easy direction of the Fundamental
  Theorem of Tropical Geometry (tropicalization ⊆ corner locus), and
* `TropicalValuationBridge.TropPoly.eval_mul` — min-plus multiplicativity
  `eval (P ⊙ Q) = eval P + eval Q`, the *engine* of tropical Bézout.

To keep this file self-contained (and to let it be checked in isolation) we re-state the two
small pieces of vocabulary from that bridge file — the corner-locus predicate
`AttainedAtLeastTwice` and the `TropPoly` structure with its tropical product `TropPoly.mul` —
and then prove the genuinely new **tropical Bézout / factorization** theorems on top of them.

## Main results

* `TropicalBezout.attainedTwice_smul` — **scale invariance of the corner locus**
  (the "valuation → ∞" limit).  Rescaling all weights by a positive constant `t` (as happens
  when the valuation `v` is replaced by `t · v`) does not change the corner locus.  This is the
  precise sense in which the tropical variety is the scale-invariant *limit* of the family of
  amoebas.  It complements `kapranov_easy_direction`, which produces a corner from a single `v`.

* `TropicalBezout.tropRoot_mul_iff` — **the tropical hypersurface of a product is the union of
  the hypersurfaces.**  A point is a tropical root of `P ⊙ Q` iff it is a tropical root of `P` or
  of `Q`.  Combined with `eval_mul` (degrees add), this is the combinatorial core of the tropical
  Bézout theorem: a degree-`d`·degree-`e` intersection decomposes into the right count of pieces.

* `TropicalBezout.tropRootSet_mul` — the set-level restatement `V(P ⊙ Q) = V(P) ∪ V(Q)`.

* `TropicalBezout.range_exp_mul` — **Newton polytopes add (Minkowski sum).**  The exponent
  support of `P ⊙ Q` is the Minkowski sum of the supports of `P` and `Q`.  This is the
  polytope-level shadow of degree additivity underlying Bézout's degree count.

* A boundary case (`tropRoot_mul_subsingleton_right`): multiplying by a single tropical monomial
  adds no roots.
-/

open Finset
open scoped Pointwise

open TropicalBezout

/-! ## §0. Vocabulary inherited from the bridge file (re-stated for self-containment) -/





/-
!-- A single index can never witness `i ≠ j`. -- !--
A one-monomial tropical polynomial has empty corner locus.  Mirrors
`TropicalValuationBridge.attainedTwice_subsingleton`.
-/

/-! ## §1. Scale invariance of the corner locus — the "valuation → ∞" limit -/

/-
!-- Multiplying every weight by a fixed `t > 0` is an order isomorphism on `ℝ`, so
`t * w i ≤ t * w k ↔ w i ≤ w k`; the witnessing indices of the corner are therefore unchanged. -- !--

**Scale invariance (the limiting tropical shape).**  Classically one studies the rescaled
valuations `v_t = t · v` as `t → ∞`.  The corner-locus predicate `AttainedAtLeastTwice` is
invariant under such a positive rescaling, so the tropical variety is genuinely the
scale-independent limit of the family.
-/

/-! ## §2. The general combinatorial lemma: minimizers of a separated sum -/

/-
!-- A pair `(i,k)` minimizes `a i + b k` iff `i` minimizes `a` and `k` minimizes `b`; the
minimizing set is the product of the two minimizing sets, which has ≥ 2 elements iff one factor
does.  Minimizers of `a` and `b` exist by finiteness. -- !--

**Separated-sum corner lemma.**  For a function of the form `(i,k) ↦ a i + b k` on a product of
finite nonempty types, the corner-locus condition holds iff it holds for `a` or for `b`.  This is
the engine behind the tropical factorization theorem below.
-/

theorem TropicalBezout.attainedTwice_add_iff{ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (a : ι → ℝ) (b : κ → ℝ) :
    AttainedAtLeastTwice (fun p : ι × κ => a p.1 + b p.2)
      ↔ AttainedAtLeastTwice a ∨ AttainedAtLeastTwice b := by sorry
