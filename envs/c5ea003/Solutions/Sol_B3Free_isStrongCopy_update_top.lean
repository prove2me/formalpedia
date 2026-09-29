-- Prove2me | solution 1 for B3Free.isStrongCopy_update_top
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:26:02.057713+00:00
-- url     : https://prove2.me/submissions/8a7469ca-bfec-4f4b-a11a-f7e0b32835b0

-- Sol generated from Bridges/B3FreeFamiliesBounds.lean
import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
import Definitions.Def_Bridges_B3FreeFamiliesBounds
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Maximality of layer families, exact values, and a general upper bound for `La(n, B_d)`

This file continues `Catalog/Bridges/B3FreeFamilies.lean`, which sets up the framework of
weak/strong `P`-free families surrounding the paper *On the maximum size of `B_3`-free
families*.

## Main results

* `not_strongFree_insert_layers`, `layers_maximal_weakFree`, `layers_maximal_strongFree` —
  **maximality of the layer construction**: adding to `d` consecutive layers any set whose
  size lies outside the corresponding interval creates a strong (hence weak) copy of `B_d`.
  Consequently an `ε`-improvement can never be obtained by enlarging the layer family.
* `La_boolLat_eq_of_card_eq_succ`, `LaStar_boolLat_eq_of_card_eq_succ`, `La_boolLat3_fin4` —
  the exact value `La(d+1, B_d) = La*(d+1, B_d) = 2^(d+1) - 2`, attained by the `d` layers
  `1, …, d`; in particular `La(4, B_3) = 14`.  Hence `La` and `La*` agree for `n ∈ {d, d+1}`
  (`La_eq_LaStar_of_card_eq_succ`).
* `La_boolLat_lt_succ_of_card_eq_succ`, `La_boolLat3_lt_boolLat4_fin4` — strict
  monotonicity `La(d+1, B_d) < La(d+1, B_(d+1))`.
* `not_hasChain_of_weakFree`, `card_le_of_not_hasChain`, `La_boolLat_le` — a chain of
  `2^d` sets contains a weak copy of `B_d`, and a Mirsky-type peeling of maximal sets
  combined with Sperner's theorem gives the **general upper bound**
  `La(n, B_d) ≤ (2^d - 1) · C(n, ⌊n/2⌋)`; for `d = 3` this brackets the paper's quantity,
  `3 · C(n, ⌊n/2⌋-2) ≤ La(n, B_3) ≤ 7 · C(n, ⌊n/2⌋)` (`La_boolLat3_bounds`).
-/


open B3Free

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Maximality of the layer families

The `d`-layer construction is not only weak `B_d`-free: it is a *maximal* such
family.  Adding any further set to `layers α a d` creates a strong (hence also a
weak) copy of `B_d`.  So the `ε`-improvement of Ellis–Ivan–Leader (and of the
`B_3` paper) can never be obtained by enlarging the layer family; sets have to be
deleted first.
-/


variable {d : ℕ}













/-! ## An exact value: ground set of size `d + 1`

On a ground set with `d + 1` elements the extremal family is again a family of
layers, namely all sets except `∅` and the ground set: `La(d+1, B_d) = 2^(d+1) - 2`.
-/


variable {d : ℕ}










/-! ## Chains, Mirsky-type partitions, and a general upper bound

A chain of `2^d` sets already contains a weak copy of `B_d` (map `B_d` into the chain
along the binary-encoding linear extension), so a weak `B_d`-free family has no chain of
`2^d` sets.  Peeling off maximal elements (a Mirsky-type argument) and applying Sperner's
theorem to each layer of maximal elements gives the general upper bound
`La(n, B_d) ≤ (2^d − 1) · C(n, ⌊n/2⌋)`.
-/





















open B3Free in
omit [DecidableEq α] [Fintype α] in
theorem solution{ι : BoolLat d → Finset α} (h : IsStrongCopy ι)
    (A : Finset α) (hlt : ∀ X : BoolLat d, X ≠ Finset.univ → ι X ⊂ A) :
    IsStrongCopy (fun X : BoolLat d => if X = Finset.univ then A else ι X) := by
  classical
  constructor
  · intro X Y hXY
    simp only at hXY
    by_cases hX : X = Finset.univ <;> by_cases hY : Y = Finset.univ
    · rw [hX, hY]
    · rw [if_pos hX, if_neg hY] at hXY
      exact absurd hXY.symm (hlt Y hY).ne
    · rw [if_neg hX, if_pos hY] at hXY
      exact absurd hXY (hlt X hX).ne
    · rw [if_neg hX, if_neg hY] at hXY
      exact h.1 hXY
  · intro X Y
    simp only
    by_cases hX : X = Finset.univ <;> by_cases hY : Y = Finset.univ
    · rw [if_pos hX, if_pos hY, hX, hY]
      exact ⟨fun hc => absurd rfl hc.ne, fun hc => absurd rfl hc.ne⟩
    · rw [if_pos hX, if_neg hY, hX]
      refine iff_of_false (fun hc => absurd (hlt Y hY) (asymm hc)) ?_
      intro hc
      exact hY (Finset.univ_subset_iff.1 (Finset.lt_iff_ssubset.1 hc).subset)
    · rw [if_neg hX, if_pos hY, hY]
      refine iff_of_true (hlt X hX) ?_
      simpa [Finset.lt_iff_ssubset] using Finset.ssubset_univ_iff.2 hX
    · rw [if_neg hX, if_neg hY]
      exact h.2 X Y
