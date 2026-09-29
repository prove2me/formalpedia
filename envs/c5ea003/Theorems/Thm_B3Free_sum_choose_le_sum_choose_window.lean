-- Prove2me | Theorems.Thm_B3Free_sum_choose_le_sum_choose_window
-- name    : B3Free.sum_choose_le_sum_choose_window
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:13:56.491537+00:00
-- url     : https://prove2.me/theorems/0d4d0534-29bd-44ad-8801-08628f8d34a7
-- title:
--   The best `d` levels are `d` consecutive central levels.
-- statement:
--   **The best `d` levels are `d` consecutive central levels.**  For any set `S` of at most
--   `d` levels, the total number of sets on the levels of `S` is at most the number of sets on
--   the `d` central levels.
--
--   ```lean
--   theorem B3Free.sum_choose_le_sum_choose_window{n d : ℕ} (hdn : d ≤ n + 1)
--       {S : Finset ℕ} (hS : S.card ≤ d) :
--       ∑ i ∈ S, n.choose i ≤
--         ∑ i ∈ Finset.Ico (centralStart n d) (centralStart n d + d), n.choose i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/B3FreeFamiliesLevels.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/B3FreeFamiliesLevels.lean#L400

-- Thm stub generated from Bridges/B3FreeFamiliesLevels.lean
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

theorem B3Free.sum_choose_le_sum_choose_window{n d : ℕ} (hdn : d ≤ n + 1)
    {S : Finset ℕ} (hS : S.card ≤ d) :
    ∑ i ∈ S, n.choose i ≤
      ∑ i ∈ Finset.Ico (centralStart n d) (centralStart n d + d), n.choose i := by sorry
