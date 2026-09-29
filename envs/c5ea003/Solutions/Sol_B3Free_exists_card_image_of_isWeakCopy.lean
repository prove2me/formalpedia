-- Prove2me | solution 1 for B3Free.exists_card_image_of_isWeakCopy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:31:52.48014+00:00
-- url     : https://prove2.me/submissions/793dcbea-7a17-46aa-ab0a-2bf038649fb3

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
omit [DecidableEq α] [Fintype α] in
theorem solution{d : ℕ} {ι : BoolLat d → Finset α}
    (h : IsWeakCopy ι) :
    ∃ T : Finset ℕ, T.card = d + 1 ∧ ∀ m ∈ T, ∃ X : BoolLat d, (ι X).card = m := by
  classical
  set S : ℕ → BoolLat d := fun k => Finset.univ.filter (fun i : Fin d => (i : ℕ) < k) with hS
  have hchain : ∀ k, k < d → S k < S (k + 1) := by
    intro k hk
    refine lt_of_le_of_ne ?_ ?_
    · intro i hi
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      omega
    · intro hEq
      have : (⟨k, hk⟩ : Fin d) ∈ S (k + 1) := by simp [hS]
      rw [← hEq] at this
      simp [hS] at this
  have hmono : ∀ j k, j ≤ k → k ≤ d → (ι (S j)).card + (k - j) ≤ (ι (S k)).card := by
    intro j k hjk
    induction k with
    | zero => intro _; simp_all
    | succ m ih =>
      intro hm
      rcases Nat.lt_or_ge j (m + 1) with hlt | hge
      · have h1 := ih (by omega) (by omega)
        have h2 : ι (S m) ⊂ ι (S (m + 1)) := h.2 _ _ (hchain m (by omega))
        have h3 := Finset.card_lt_card h2
        omega
      · have : j = m + 1 := by omega
        subst this
        simp
  refine ⟨(Finset.range (d + 1)).image (fun k => (ι (S k)).card), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro j hj k hk hjk
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    have hjk' : (ι (S j)).card = (ι (S k)).card := hjk
    by_contra hne
    rcases Nat.lt_or_ge j k with hlt | hge
    · have := hmono j k (le_of_lt hlt) (by omega)
      omega
    · have hlt : k < j := by omega
      have := hmono k j (le_of_lt hlt) (by omega)
      omega
  · intro m hm
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hm
    exact ⟨S k, rfl⟩
