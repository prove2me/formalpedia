-- Prove2me | solution 1 for B3Free.exists_strongCopy_levelFamily
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:31:53.671086+00:00
-- url     : https://prove2.me/submissions/07e2441e-69dd-4f33-acaa-bc976371b809

-- Sol generated from Bridges/B3FreeFamiliesLevels.lean
import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
import Definitions.Def_Bridges_B3FreeFamiliesLevels
import Theorems.Thm_B3Free_exists_strongCopy_of_levels
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


theorem mem_levelFamily {S : Finset ℕ} {A : Finset α} :
    A ∈ levelFamily α S ↔ A.card ∈ S := by
  simp [levelFamily]




/-! ## A weak copy of `B_d` realizes `d + 1` distinct levels -/



/-! ## A strong copy of `B_d` spread over `d + 1` arbitrary levels -/


variable {d : ℕ}








/-! ## Which level families are `B_d`-free -/






/-! ## Unimodality of the binomial row and the optimal window of levels -/





/-! ## The level-restricted extremal number -/




/-! ## Permutation-invariant families -/









/-! ## Two easy complements -/









open B3Free in
theorem solution{d : ℕ} {S : Finset ℕ}
    (hS : d + 1 ≤ (S.filter (· ≤ Fintype.card α)).card) :
    ∃ ι : BoolLat d → Finset α, IsStrongCopy ι ∧ ∀ X, ι X ∈ levelFamily α S := by
  classical
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := S.filter (· ≤ Fintype.card α)) (n := d + 1) hS
  set iso := T.orderIsoOfFin hTcard with hiso
  set t : ℕ → ℕ := fun k => (iso ⟨min k d, by omega⟩ : ℕ) with ht
  have hmemT : ∀ k, t k ∈ T := fun k => (iso ⟨min k d, by omega⟩).2
  have hstep : ∀ k < d, t k < t (k + 1) := by
    intro k hk
    have hlt : (⟨min k d, by omega⟩ : Fin (d + 1)) < ⟨min (k + 1) d, by omega⟩ := by
      simp only [Fin.mk_lt_mk]
      omega
    have := (iso.lt_iff_lt).2 hlt
    simpa [ht] using this
  have hlast : t d ≤ Fintype.card α := by
    have := hTsub (hmemT d)
    simpa using (Finset.mem_filter.1 this).2
  obtain ⟨ι, hι, hcard⟩ := exists_strongCopy_of_levels (α := α) (d := d) t hstep hlast
  refine ⟨ι, hι, fun X => ?_⟩
  rw [mem_levelFamily, hcard X]
  exact (Finset.mem_filter.1 (hTsub (hmemT X.card))).1
