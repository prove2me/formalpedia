-- Prove2me | Theorems.Thm_sortChord_exists_perm
-- name    : sortChord_exists_perm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-16T20:35:30.052292+00:00
-- url     : https://prove2.me/theorems/29f295dc-28ae-40f9-a4c9-31092866eef8
-- title:
--   SortChord exists perm
-- statement:
--   Formal statement of `sortChord_exists_perm` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem sortChord_exists_perm{n : ℕ} (x : Fin n → ℤ) :
--       ∃ σ : Equiv.Perm (Fin n), ∀ i, sortChord x i = x (σ i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/VoiceLeadingSorted.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/VoiceLeadingSorted.lean#L77

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

theorem sortChord_exists_perm{n : ℕ} (x : Fin n → ℤ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, sortChord x i = x (σ i) := by sorry
