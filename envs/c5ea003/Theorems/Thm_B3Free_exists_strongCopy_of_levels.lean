-- Prove2me | Theorems.Thm_B3Free_exists_strongCopy_of_levels
-- name    : B3Free.exists_strongCopy_of_levels
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:13:24.108264+00:00
-- url     : https://prove2.me/theorems/7412981c-efed-48ad-a88c-78a5b84b4203
-- title:
--   Strong copies over arbitrary levels.
-- statement:
--   **Strong copies over arbitrary levels.**  If `t 0 < t 1 < ⋯ < t d ≤ n` are `d + 1`
--   levels, then the sets of these levels contain a strong copy of `B_d` whose element of rank
--   `k` has size exactly `t k`.  For `t k = a + k` this is `exists_strongCopy_layers`.
--
--   ```lean
--   theorem B3Free.exists_strongCopy_of_levels{d : ℕ} (t : ℕ → ℕ)
--       (hstep : ∀ k < d, t k < t (k + 1)) (hlast : t d ≤ Fintype.card α) :
--       ∃ ι : BoolLat d → Finset α, IsStrongCopy ι ∧ ∀ X : BoolLat d, (ι X).card = t X.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/B3FreeFamiliesLevels.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/B3FreeFamiliesLevels.lean#L205

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







omit [DecidableEq α] in

theorem B3Free.exists_strongCopy_of_levels{d : ℕ} (t : ℕ → ℕ)
    (hstep : ∀ k < d, t k < t (k + 1)) (hlast : t d ≤ Fintype.card α) :
    ∃ ι : BoolLat d → Finset α, IsStrongCopy ι ∧ ∀ X : BoolLat d, (ι X).card = t X.card := by sorry
