-- Prove2me | Definitions.Def_Bridges_VoiceLeadingSorted
-- name    : Bridges_VoiceLeadingSorted
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:28:31.447851+00:00
-- url     : https://prove2.me/theorems/7c095858-6c55-417c-924f-25b0fd25d8b4
-- title:
--   Aether Catalog definitions — Bridges_VoiceLeadingSorted
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.VoiceLeadingSorted`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/VoiceLeadingSorted.lean by skeleton subtraction
import Mathlib
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

/-- Sort a chord (Fin n → ℤ) into weakly increasing order using merge sort.
    This is the canonical representative of the chord's permutation orbit. -/
def sortChord {n : ℕ} (x : Fin n → ℤ) : Fin n → ℤ :=
  fun i => (List.insertionSort (fun a b => decide (a ≤ b)) (List.ofFn x))[i.val]'(by simp)

/-- The voice-leading cost between two chords: the minimum over all voice permutations
    of the sum of absolute pitch differences. -/
noncomputable def vlCostN {n : ℕ} (x y : Fin n → ℤ) : ℕ :=
  Finset.inf' Finset.univ ⟨1, Finset.mem_univ 1⟩
    (fun σ : Equiv.Perm (Fin n) => ∑ i : Fin n, Int.natAbs (x i - y (σ i)))

/-- Computable voice-leading cost: sort both chords and sum coordinatewise distances. -/
def vlCostN_compute {n : ℕ} (x y : Fin n → ℤ) : ℕ :=
  ∑ i : Fin n, Int.natAbs (sortChord x i - sortChord y i)

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

/-! ## Quotient structure -/

/-
Two chords are in the same permutation orbit iff they have the same sorted form.
-/

/-! ## Computational Examples -/



/-- Sorting reorders unsorted chords. -/
example : sortChord (![3, 1, 4, 1] : Fin 4 → ℤ) = ![1, 1, 3, 4] := by decide


