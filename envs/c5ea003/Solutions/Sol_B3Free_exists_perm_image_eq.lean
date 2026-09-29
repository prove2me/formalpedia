-- Prove2me | solution 1 for B3Free.exists_perm_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:31:53.064108+00:00
-- url     : https://prove2.me/submissions/54a89ceb-ebf2-47fb-8cc8-489fcb2fb867

-- Sol generated from Bridges/B3FreeFamiliesLevels.lean
import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
import Definitions.Def_Bridges_B3FreeFamiliesLevels
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Level (size-determined) families and the exact level-restricted extremal number

This file continues `Catalog/Bridges/B3FreeFamilies.lean` and
`Catalog/Bridges/B3FreeFamiliesBounds.lean`, which set up the framework of weak/strong
`P`-free families surrounding the paper *On the maximum size of `B_3`-free families*.

The paper's headline result is that `La(n, B_3) ≥ (3 + ε) C(n, ⌊n/2⌋)` for some absolute
`ε > 0`, i.e. that the three-layer construction is *not* optimal.  Here we prove a
complementary structural statement: **no improvement at all can come from a family that is
determined by the sizes of its sets** — equivalently, from a family invariant under the
permutations of the ground set.  Among all such families the `d` central layers are exactly
optimal.

## Main results

* `levelFamily` — the family of all subsets whose size lies in a prescribed set `S` of
  levels, and `card_levelFamily : |𝓛(S)| = ∑_{i ∈ S} C(n, i)`.
* `exists_strongCopy_levelFamily` — if `S` contains `d + 1` levels that are realized in
  `2^[n]`, then `𝓛(S)` contains a *strong* copy of `B_d`.  The levels need **not** be
  consecutive; this generalizes `exists_strongCopy_layers`.
* `levelFamily_weakFree_iff`, `levelFamily_strongFree_iff` — `𝓛(S)` is weak (strong)
  `B_d`-free **iff** at most `d` levels of `S` are realized.
* `sum_choose_le_sum_choose_window` — for a unimodal binomial row, any `d` levels have total
  weight at most that of `d` consecutive levels around the middle.
* `card_levelFamily_le_layers`, `level_extremal` — **exact level-restricted
  extremal number**: a weak `B_d`-free level family has at most `|layers α a d|` sets, for
  the central window `a`, and this is attained.
* `symmetric_weakFree_card_le`, `symmetric_weakFree_card_le_mul` — the same bound for every
  permutation-invariant weak `B_d`-free family, and the clean corollary
  `|F| ≤ d · C(n, ⌊n/2⌋)`: the `ε`-improvement of the paper must break the symmetry of the
  cube.
* `La_boolLat_eq_two_pow_of_lt`, `LaStar_boolLat_eq_two_pow_of_lt` — the degenerate range
  `n < d`, where the whole power set is `B_d`-free.
* `strongFree_boolLatOne_iff`, `LaStar_boolLatOne_eq` — Sperner's theorem also for the
  strong extremal function, `La*(n, B_1) = C(n, ⌊n/2⌋)`.
-/


open B3Free

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Level families -/






/-! ## A weak copy of `B_d` realizes `d + 1` distinct levels -/



/-! ## A strong copy of `B_d` spread over `d + 1` arbitrary levels -/


variable {d : ℕ}








/-! ## Which level families are `B_d`-free -/






/-! ## Unimodality of the binomial row and the optimal window of levels -/





/-! ## The level-restricted extremal number -/




/-! ## Permutation-invariant families -/









/-! ## Two easy complements -/









open B3Free in
theorem solution{A B : Finset α} (h : A.card = B.card) :
    ∃ e : Equiv.Perm α, A.image e = B := by
  classical
  have hA : Fintype.card {a : α // a ∈ A} = Fintype.card {a : α // a ∈ B} := by
    simpa using h
  have hAc : Fintype.card {a : α // a ∉ A} = Fintype.card {a : α // a ∉ B} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hA]
  obtain ⟨e1⟩ : Nonempty ({a : α // a ∈ A} ≃ {a : α // a ∈ B}) := ⟨Fintype.equivOfCardEq hA⟩
  obtain ⟨e2⟩ : Nonempty ({a : α // a ∉ A} ≃ {a : α // a ∉ B}) := ⟨Fintype.equivOfCardEq hAc⟩
  refine ⟨(Equiv.sumCompl (· ∈ A)).symm.trans
    ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (· ∈ B))), ?_⟩
  have hsub : A.image ((Equiv.sumCompl (· ∈ A)).symm.trans
      ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (· ∈ B)))) ⊆ B := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos ha,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact (e1 ⟨a, ha⟩).2
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [Finset.card_image_of_injective _ (Equiv.injective _), ← h]
