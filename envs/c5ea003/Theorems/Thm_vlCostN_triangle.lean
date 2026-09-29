-- Prove2me | Theorems.Thm_vlCostN_triangle
-- name    : vlCostN_triangle
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-16T20:35:36.992333+00:00
-- url     : https://prove2.me/theorems/b61f86cf-2c98-4532-a923-29d6d9529ee6
-- title:
--   VlCostN triangle
-- statement:
--   Formal statement of `vlCostN_triangle` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem vlCostN_triangle{n : ℕ} (x y z : Fin n → ℤ) :
--       vlCostN x z ≤ vlCostN x y + vlCostN y z := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/VoiceLeadingSorted.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/VoiceLeadingSorted.lean#L238

-- Thm stub generated from Bridges/VoiceLeadingSorted.lean
import Mathlib
import Definitions.Def_Bridges_VoiceLeadingSorted
/-
# Sorted Canonical Representatives for Voice-Leading Geometry

This file establishes that the quotient metric on chord space (under permutation of voices)
is exactly computed by sorting both chords and summing coordinatewise absolute differences.
This is a formalization of the discrete 1D optimal transport theorem / rearrangement inequality
applied to music-theoretic voice leading.

## Main Results

* `sortChord` — Canonical sorted representative of a chord's permutation orbit.
* `sortChord_monotone` — The sorted representative is monotone (weakly increasing).
* `sortChord_perm` — The sorted representative is a permutation of the original.
* `vlCostN` — Voice-leading cost: minimum over all permutations of coordinatewise |·|.
* `vlCostN_perm_left` / `vlCostN_perm_right` — Permutation invariance on both arguments.
* `vlCostN_eq_sorted_pairing` — **Main theorem**: the voice-leading cost equals the
  coordinatewise L¹ distance between sorted representatives.
* `vlCostN_compute` / `vlCostN_compute_correct` — Certified computable evaluator.

## Mathematical Significance

The key conceptual move is to replace an abstract quotient by a canonical section: the
sorted representative. The main theorem shows this representative preserves the quotient
metric exactly, turning the voice-leading cost from an existential (infimum over n!
permutations) into an explicit O(n log n) computation: sort and sum.

This is the finite-dimensional shadow of optimal transport theory: monotone coupling
minimizes Wasserstein-1 cost in one dimension.
-/

open Finset Equiv

/-! ## Definitions -/




/-! ## Properties of sortChord -/


/-
The sorted chord is monotone (weakly increasing).
-/


/-
There exists a permutation σ such that sortChord x = x ∘ σ.
-/

/-
Sorting is invariant under permutation of the input.
-/

/-! ## Permutation invariance of vlCostN -/

/-
The voice-leading cost is invariant under permutation of the left argument.
-/

/-
The voice-leading cost is invariant under permutation of the right argument.
-/


/-! ## Core: vlCostN equals sorted pairing -/



/-
**Main Theorem.** The voice-leading cost equals the coordinatewise L¹ distance
    between sorted representatives. This identifies the quotient metric with
    the L¹ metric on the sorted Weyl chamber.
-/


/-! ## Additional properties -/


/-
The voice-leading cost is symmetric.
-/

/-
The voice-leading cost satisfies the triangle inequality.
-/

theorem vlCostN_triangle{n : ℕ} (x y z : Fin n → ℤ) :
    vlCostN x z ≤ vlCostN x y + vlCostN y z := by sorry
