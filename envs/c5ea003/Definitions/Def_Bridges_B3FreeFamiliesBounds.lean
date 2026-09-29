-- Prove2me | Definitions.Def_Bridges_B3FreeFamiliesBounds
-- name    : Bridges_B3FreeFamiliesBounds
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:12.100467+00:00
-- url     : https://prove2.me/theorems/32481fad-62c5-4f34-ab88-af5523e845e4
-- title:
--   Aether Catalog definitions — Bridges_B3FreeFamiliesBounds
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.B3FreeFamiliesBounds`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/B3FreeFamiliesBounds.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
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


namespace B3Free

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Maximality of the layer families

The `d`-layer construction is not only weak `B_d`-free: it is a *maximal* such
family.  Adding any further set to `layers α a d` creates a strong (hence also a
weak) copy of `B_d`.  So the `ε`-improvement of Ellis–Ivan–Leader (and of the
`B_3` paper) can never be obtained by enlarging the layer family; sets have to be
deleted first.
-/

section Maximality

variable {d : ℕ}












end Maximality

/-! ## An exact value: ground set of size `d + 1`

On a ground set with `d + 1` elements the extremal family is again a family of
layers, namely all sets except `∅` and the ground set: `La(d+1, B_d) = 2^(d+1) - 2`.
-/

section CardSucc

variable {d : ℕ}









end CardSucc

/-! ## Chains, Mirsky-type partitions, and a general upper bound

A chain of `2^d` sets already contains a weak copy of `B_d` (map `B_d` into the chain
along the binary-encoding linear extension), so a weak `B_d`-free family has no chain of
`2^d` sets.  Peeling off maximal elements (a Mirsky-type argument) and applying Sperner's
theorem to each layer of maximal elements gives the general upper bound
`La(n, B_d) ≤ (2^d − 1) · C(n, ⌊n/2⌋)`.
-/

section Chains

/-- `F` contains a chain of `k` sets. -/
def HasChain (F : Finset (Finset α)) (k : ℕ) : Prop :=
  ∃ c : Fin k → Finset α, StrictMono c ∧ ∀ i, c i ∈ F

theorem sum_range_two_pow (m : ℕ) : ∑ i ∈ Finset.range m, 2 ^ i = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Finset.sum_range_succ, ih]
    omega

theorem sum_two_pow_lt {d : ℕ} (X : BoolLat d) : ∑ i ∈ X, 2 ^ (i : ℕ) < 2 ^ d := by
  have h1 : ∑ i ∈ X, 2 ^ (i : ℕ) ≤ ∑ i ∈ (Finset.univ : Finset (Fin d)), 2 ^ (i : ℕ) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ X)
  have h2 : ∑ i ∈ (Finset.univ : Finset (Fin d)), 2 ^ (i : ℕ) = 2 ^ d - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) d, sum_range_two_pow]
  have h3 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  omega

/-- The binary encoding `X ↦ ∑_{i ∈ X} 2^i` is a linear extension of `B_d`. -/
def boolLatEncode {d : ℕ} (X : BoolLat d) : Fin (2 ^ d) :=
  ⟨∑ i ∈ X, 2 ^ (i : ℕ), sum_two_pow_lt X⟩




/-- The maximal members of a family. -/
def maxSets (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter (fun A => ∀ B ∈ F, ¬ A ⊂ B)








end Chains



end B3Free


