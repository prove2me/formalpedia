-- Prove2me | solution 1 for B3Free.exists_strongCopy_avoiding
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:24:53.180542+00:00
-- url     : https://prove2.me/submissions/ccc62cac-c5d4-437d-9766-f3838dbf507c

-- Sol generated from Bridges/B3FreeFamiliesBounds.lean
import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
import Definitions.Def_Bridges_B3FreeFamiliesBounds
import Theorems.Thm_B3Free_isStrongCopy_union_image
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




/-- If `s` leaves room for `d` more elements, one finds `d` distinct elements outside `s`. -/
theorem exists_atoms_outside {s : Finset α} (h : s.card + d ≤ Fintype.card α) :
    ∃ f : Fin d → α, Function.Injective f ∧ ∀ i, f i ∉ s := by
  classical
  have hcard : d ≤ (Finset.univ \ s).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 (Finset.subset_univ s), Finset.card_univ]
    omega
  obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨e⟩ : Nonempty (Fin d ≃ (u : Finset α)) := ⟨(Finset.equivFinOfCardEq hucard).symm⟩
  refine ⟨fun i => (e i : α), fun i j hij => e.injective (Subtype.ext hij), fun i => ?_⟩
  have h2 := hu (e i).2
  simp only [Finset.mem_sdiff] at h2
  exact h2.2









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
theorem solution(hcard : Fintype.card α = d + 1) (A : Finset α) :
    ∃ ι : BoolLat d → Finset α, IsStrongCopy ι ∧ ∀ X, ι X ≠ A := by
  classical
  rcases Finset.eq_empty_or_nonempty A with rfl | ⟨j, hj⟩
  · obtain ⟨j⟩ : Nonempty α := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨f, hf, hdisj⟩ := exists_atoms_outside (s := ({j} : Finset α)) (d := d)
      (by rw [Finset.card_singleton, hcard]; omega)
    refine ⟨fun X => {j} ∪ X.image f, isStrongCopy_union_image _ f hf hdisj, fun X hX => ?_⟩
    simp only at hX
    have hmem : j ∈ ({j} : Finset α) ∪ X.image f :=
      Finset.mem_union_left _ (Finset.mem_singleton_self j)
    rw [hX] at hmem
    simp at hmem
  · obtain ⟨f, hf, hdisj⟩ := exists_atoms_outside (s := ({j} : Finset α)) (d := d)
      (by rw [Finset.card_singleton, hcard]; omega)
    have hdisj' : ∀ i, f i ∉ (∅ : Finset α) := by simp
    refine ⟨fun X => ∅ ∪ X.image f, isStrongCopy_union_image _ f hf hdisj', fun X hX => ?_⟩
    simp only at hX
    have hjn : j ∉ (∅ : Finset α) ∪ X.image f := by
      simp only [Finset.empty_union, Finset.mem_image]
      rintro ⟨i, -, rfl⟩
      exact hdisj i (Finset.mem_singleton_self _)
    rw [hX] at hjn
    exact hjn hj
