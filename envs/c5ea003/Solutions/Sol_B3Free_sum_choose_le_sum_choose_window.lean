-- Prove2me | solution 1 for B3Free.sum_choose_le_sum_choose_window
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:34:12.684607+00:00
-- url     : https://prove2.me/submissions/7d87773c-2f74-43cf-b426-25f6986c4758

-- Sol generated from Bridges/B3FreeFamiliesLevels.lean
import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
import Definitions.Def_Bridges_B3FreeFamiliesLevels
import Theorems.Thm_B3Free_choose_le_choose_of_le_half
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

/-- If `i ≤ j` and `i + j ≤ n`, then `j` is at least as close to the middle of the `n`-th
binomial row as `i`, hence `C(n, i) ≤ C(n, j)`. -/
theorem choose_le_choose_of_add_le {n i j : ℕ} (hij : i ≤ j) (hsum : i + j ≤ n) :
    n.choose i ≤ n.choose j := by
  rcases Nat.lt_or_ge (n / 2) j with hj | hj
  · have hjn : j ≤ n := by omega
    have h1 : n - j ≤ n / 2 := by omega
    have h2 : i ≤ n - j := by omega
    have := choose_le_choose_of_le_half h2 h1
    rwa [Nat.choose_symm hjn] at this
  · exact choose_le_choose_of_le_half hij hj

/-- The mirror image of `choose_le_choose_of_add_le`: if `j ≤ i` and `n ≤ i + j`, then
`C(n, i) ≤ C(n, j)`. -/
theorem choose_le_choose_of_le_add {n i j : ℕ} (hji : j ≤ i) (hsum : n ≤ i + j) :
    n.choose i ≤ n.choose j := by
  rcases Nat.lt_or_ge n i with hin | hin
  · simp [Nat.choose_eq_zero_of_lt hin]
  · have hjn : j ≤ n := le_trans hji hin
    have h1 : n - i ≤ n - j := by omega
    have h2 : (n - i) + (n - j) ≤ n := by omega
    have := choose_le_choose_of_add_le h1 h2
    rwa [Nat.choose_symm hin, Nat.choose_symm hjn] at this



/-! ## The level-restricted extremal number -/




/-! ## Permutation-invariant families -/









/-! ## Two easy complements -/









open B3Free in
theorem solution{n d : ℕ} (hdn : d ≤ n + 1)
    {S : Finset ℕ} (hS : S.card ≤ d) :
    ∑ i ∈ S, n.choose i ≤
      ∑ i ∈ Finset.Ico (centralStart n d) (centralStart n d + d), n.choose i := by
  classical
  set a := centralStart n d with ha
  set W := Finset.Ico a (a + d) with hW
  have ha1 : n ≤ 2 * a + d := by
    simp only [ha, centralStart]
    omega
  have ha2 : 2 * a + d ≤ n + 1 := by
    simp only [ha, centralStart]
    omega
  have hWcard : W.card = d := by simp [hW]
  -- every level outside the window is dominated by every level inside it
  have key : ∀ s ∈ S \ W, ∀ w ∈ W, n.choose s ≤ n.choose w := by
    intro s hs w hw
    rw [Finset.mem_sdiff] at hs
    rw [hW, Finset.mem_Ico] at hw
    have hsW : ¬ (a ≤ s ∧ s < a + d) := by
      intro h
      exact hs.2 (by rw [hW, Finset.mem_Ico]; exact h)
    rcases Nat.lt_or_ge s a with hlt | hge
    · exact choose_le_choose_of_add_le (by omega) (by omega)
    · have hs' : a + d ≤ s := by omega
      exact choose_le_choose_of_le_add (by omega) (by omega)
  -- the part of `S` outside the window is no bigger than the part of the window outside `S`
  have hcard : (S \ W).card ≤ (W \ S).card := by
    have h1 := Finset.card_inter_add_card_sdiff S W
    have h2 := Finset.card_inter_add_card_sdiff W S
    have h3 : (W ∩ S).card = (S ∩ W).card := by rw [Finset.inter_comm]
    omega
  have hdiff : ∑ i ∈ S \ W, n.choose i ≤ ∑ i ∈ W \ S, n.choose i := by
    rcases Finset.eq_empty_or_nonempty (S \ W) with hemp | hne
    · simp [hemp]
    · have hne' : (W \ S).Nonempty := Finset.card_pos.1 (by
        have := Finset.card_pos.2 hne
        omega)
      obtain ⟨w0, hw0, hw0min⟩ := Finset.exists_min_image (W \ S) (fun i => n.choose i) hne'
      have hw0W : w0 ∈ W := (Finset.mem_sdiff.1 hw0).1
      calc ∑ i ∈ S \ W, n.choose i ≤ (S \ W).card • n.choose w0 :=
            Finset.sum_le_card_nsmul _ _ _ (fun s hs => key s hs w0 hw0W)
        _ ≤ (W \ S).card • n.choose w0 := by
            simp only [smul_eq_mul]
            exact Nat.mul_le_mul_right _ hcard
        _ ≤ ∑ i ∈ W \ S, n.choose i :=
            Finset.card_nsmul_le_sum _ _ _ (fun w hw => hw0min w hw)
  have hsplit1 : ∑ i ∈ S ∩ W, n.choose i + ∑ i ∈ S \ W, n.choose i = ∑ i ∈ S, n.choose i :=
    Finset.sum_inter_add_sum_diff S W _
  have hsplit2 : ∑ i ∈ W ∩ S, n.choose i + ∑ i ∈ W \ S, n.choose i = ∑ i ∈ W, n.choose i :=
    Finset.sum_inter_add_sum_diff W S _
  have hcomm : ∑ i ∈ W ∩ S, n.choose i = ∑ i ∈ S ∩ W, n.choose i := by rw [Finset.inter_comm]
  omega
