-- Prove2me | solution 1 for B3Free.card_le_of_not_hasChain
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:26:00.551849+00:00
-- url     : https://prove2.me/submissions/664d6ab8-13e4-46e0-8ea1-e47779fa2af9

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










theorem maxSets_subset (F : Finset (Finset α)) : maxSets F ⊆ F := Finset.filter_subset _ _

theorem isAntichain_maxSets (F : Finset (Finset α)) :
    IsAntichain (· ⊆ ·) (maxSets F : Set (Finset α)) := by
  intro A hA B hB hne hAB
  rw [Finset.mem_coe, maxSets, Finset.mem_filter] at hA hB
  exact hA.2 B hB.1 (Finset.ssubset_iff_subset_ne.2 ⟨hAB, hne⟩)

/-- Every member of a family lies below a maximal member. -/
theorem exists_maxSet_superset {F : Finset (Finset α)} {A : Finset α} (hA : A ∈ F) :
    ∃ B ∈ maxSets F, A ⊆ B := by
  classical
  obtain ⟨B, hB⟩ := Finset.exists_maximal (s := F.filter (fun C => A ⊆ C))
    ⟨A, Finset.mem_filter.2 ⟨hA, Finset.Subset.refl A⟩⟩
  have hBmem := Finset.mem_filter.1 hB.1
  refine ⟨B, Finset.mem_filter.2 ⟨hBmem.1, fun C hC hBC => ?_⟩, hBmem.2⟩
  have hCmem : C ∈ F.filter (fun C => A ⊆ C) :=
    Finset.mem_filter.2 ⟨hC, hBmem.2.trans hBC.subset⟩
  exact absurd (hB.2 hCmem hBC.subset) (by simpa using hBC.not_subset)









open B3Free in
theorem solution{k : ℕ} :
    ∀ {F : Finset (Finset α)}, ¬ HasChain F (k + 1) →
      F.card ≤ k * (Fintype.card α).choose (Fintype.card α / 2) := by
  classical
  induction k with
  | zero =>
    intro F h
    have hempty : F = ∅ := by
      by_contra hne
      obtain ⟨A, hA⟩ : ∃ A, A ∈ F := Finset.nonempty_iff_ne_empty.2 hne
      refine h ⟨fun _ => A, fun i j hij => ?_, fun _ => hA⟩
      exfalso
      have hi := i.isLt
      have hj := j.isLt
      have hij' : (i : ℕ) < (j : ℕ) := hij
      omega
    simp [hempty]
  | succ k ih =>
    intro F h
    have hsub : ¬ HasChain (F \ maxSets F) (k + 1) := by
      rintro ⟨c, hc, hmem⟩
      have hlast := hmem (Fin.last k)
      rw [Finset.mem_sdiff] at hlast
      obtain ⟨B, hBmax, hAB⟩ := exists_maxSet_superset hlast.1
      have hne : c (Fin.last k) ≠ B := fun hEq => hlast.2 (hEq ▸ hBmax)
      have hssub : c (Fin.last k) ⊂ B := Finset.ssubset_iff_subset_ne.2 ⟨hAB, hne⟩
      refine h ⟨fun i => if hi : (i : ℕ) ≤ k then c ⟨i, by omega⟩ else B, fun i j hij => ?_,
        fun i => ?_⟩
      · dsimp only
        by_cases hi : (i : ℕ) ≤ k <;> by_cases hj : (j : ℕ) ≤ k
        · rw [dif_pos hi, dif_pos hj]
          exact hc (Fin.mk_lt_mk.2 (Fin.lt_def.1 hij))
        · rw [dif_pos hi, dif_neg hj]
          have hle : (⟨i, by omega⟩ : Fin (k + 1)) ≤ Fin.last k := Fin.le_last _
          exact lt_of_le_of_lt (hc.monotone hle) (Finset.lt_iff_ssubset.2 hssub)
        · exfalso
          have h1 := i.isLt
          have h2 := j.isLt
          have h3 : (i : ℕ) < (j : ℕ) := hij
          omega
        · exfalso
          have h1 := i.isLt
          have h2 := j.isLt
          have h3 : (i : ℕ) < (j : ℕ) := hij
          omega
      · dsimp only
        by_cases hi : (i : ℕ) ≤ k
        · rw [dif_pos hi]
          exact (Finset.mem_sdiff.1 (hmem _)).1
        · rw [dif_neg hi]
          exact maxSets_subset F hBmax
    have h1 := ih hsub
    have h2 : (maxSets F).card ≤ (Fintype.card α).choose (Fintype.card α / 2) :=
      (isAntichain_maxSets F).sperner
    have h3 : (F \ maxSets F).card + (maxSets F).card = F.card := by
      rw [Finset.card_sdiff_add_card, Finset.union_eq_left.2 (maxSets_subset F)]
    have : F.card ≤ k * (Fintype.card α).choose (Fintype.card α / 2)
        + (Fintype.card α).choose (Fintype.card α / 2) := by omega
    calc F.card ≤ k * (Fintype.card α).choose (Fintype.card α / 2)
          + (Fintype.card α).choose (Fintype.card α / 2) := this
      _ = (k + 1) * (Fintype.card α).choose (Fintype.card α / 2) := by ring
