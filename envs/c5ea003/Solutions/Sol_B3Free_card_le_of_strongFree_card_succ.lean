-- Prove2me | solution 1 for B3Free.card_le_of_strongFree_card_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:24:45.113362+00:00
-- url     : https://prove2.me/submissions/013ff3a8-fd29-4a4f-be58-146e8e3f674c

-- Sol generated from Bridges/B3FreeFamiliesBounds.lean
import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
import Definitions.Def_Bridges_B3FreeFamiliesBounds
import Theorems.Thm_B3Free_StrongFree_mono
import Theorems.Thm_B3Free_exists_strongCopy_avoiding
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


/-- If `|α| = d + 1`, then removing a single set from `2^α` never yields a
strong `B_d`-free family. -/
theorem not_strongFree_erase (hcard : Fintype.card α = d + 1) (A : Finset α) :
    ¬ StrongFree ((Finset.univ : Finset (Finset α)).erase A) (BoolLat d) := by
  classical
  obtain ⟨ι, hι, hne⟩ := exists_strongCopy_avoiding hcard A
  exact fun hfree =>
    hfree ⟨ι, hι, fun X => Finset.mem_erase.2 ⟨hne X, Finset.mem_univ _⟩⟩








/-! ## Chains, Mirsky-type partitions, and a general upper bound

A chain of `2^d` sets already contains a weak copy of `B_d` (map `B_d` into the chain
along the binary-encoding linear extension), so a weak `B_d`-free family has no chain of
`2^d` sets.  Peeling off maximal elements (a Mirsky-type argument) and applying Sperner's
theorem to each layer of maximal elements gives the general upper bound
`La(n, B_d) ≤ (2^d − 1) · C(n, ⌊n/2⌋)`.
-/





















open B3Free in
theorem solution(hcard : Fintype.card α = d + 1)
    {F : Finset (Finset α)} (hF : StrongFree F (BoolLat d)) : F.card ≤ 2 ^ (d + 1) - 2 := by
  classical
  have hunivcard : (Finset.univ : Finset (Finset α)).card = 2 ^ (d + 1) := by
    simp [Finset.card_univ, hcard]
  by_contra hlt
  push_neg at hlt
  by_cases hFu : F = Finset.univ
  · exact not_strongFree_erase hcard (∅ : Finset α)
      ((hFu ▸ hF).mono (Finset.erase_subset _ _))
  · obtain ⟨A, hA⟩ : ∃ A, A ∉ F := by
      by_contra hc
      push_neg at hc
      exact hFu (Finset.eq_univ_of_forall hc)
    have hsub : F ⊆ Finset.univ.erase A := fun B hB =>
      Finset.mem_erase.2 ⟨fun hEq => hA (hEq ▸ hB), Finset.mem_univ _⟩
    have hcard2 : ((Finset.univ : Finset (Finset α)).erase A).card = 2 ^ (d + 1) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ A), hunivcard]
    have hEq : F = Finset.univ.erase A :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    exact not_strongFree_erase hcard A (hEq ▸ hF)
