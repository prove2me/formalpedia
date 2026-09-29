-- Prove2me | solution 1 for B3Free.not_strongFree_insert_of_le_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:27:59.929287+00:00
-- url     : https://prove2.me/submissions/3ad2ef42-e535-4d33-a1c3-6d59dbe32912

-- Sol generated from Bridges/B3FreeFamiliesBounds.lean
import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
import Definitions.Def_Bridges_B3FreeFamiliesBounds
import Theorems.Thm_B3Free_card_union_image
import Theorems.Thm_B3Free_exists_base_and_atoms
import Theorems.Thm_B3Free_isStrongCopy_union_image
import Theorems.Thm_B3Free_isStrongCopy_update_top
import Theorems.Thm_B3Free_mem_layers
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
theorem solution{a : ℕ} {A : Finset α} (hA : a + d ≤ A.card) :
    ¬ StrongFree (insert A (layers α a d)) (BoolLat d) := by
  classical
  obtain ⟨s, f, hf, hdisj, hs, hsA, hfA⟩ := exists_base_and_atoms (C := A) hA
  have hcopy : IsStrongCopy (fun X : BoolLat d => s ∪ X.image f) :=
    isStrongCopy_union_image s f hf hdisj
  have hcard : ∀ X : BoolLat d, (s ∪ X.image f).card = a + X.card := by
    intro X
    rw [card_union_image s f hf hdisj, hs]
  have hsub : ∀ X : BoolLat d, s ∪ X.image f ⊆ A := by
    intro X B hB
    rcases Finset.mem_union.1 hB with hB | hB
    · exact hsA hB
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hB
      exact hfA i
  have hsmall : ∀ X : BoolLat d, X ≠ Finset.univ → X.card < d := by
    intro X hX
    simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.2 hX)
  have hlt : ∀ X : BoolLat d, X ≠ Finset.univ → s ∪ X.image f ⊂ A := by
    intro X hX
    refine Finset.ssubset_iff_subset_ne.2 ⟨hsub X, fun hEq => ?_⟩
    have h1 := hcard X
    rw [hEq] at h1
    have h2 := hsmall X hX
    omega
  intro hfree
  refine hfree ⟨fun X => if X = Finset.univ then A else s ∪ X.image f,
    isStrongCopy_update_top hcopy A hlt, fun X => ?_⟩
  by_cases hX : X = Finset.univ
  · simp [hX]
  · simp only [if_neg hX]
    refine Finset.mem_insert_of_mem ?_
    rw [mem_layers, hcard X]
    have := hsmall X hX
    omega
