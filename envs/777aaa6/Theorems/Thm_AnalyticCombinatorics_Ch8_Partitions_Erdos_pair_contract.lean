-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_pair_contract
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.pair_contract
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:48:30.782165+00:00
-- url     : https://prove2.me/theorems/9f87960c-4a97-4169-aa40-5cf174fbbd15
-- title:
--   A finite-row approximate-harmonic contraction
-- statement:
--   Finite-row deterministic contraction assuming overlap and approximate harmonicity; overlap/escape inputs for the actual partition kernel remain separate.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma pair_contract {u : ℕ → ℝ} {Q : ℕ → ℕ → ℝ} {i j : ℕ} {T : Finset ℕ} {δ η lo W : ℝ}
--       (hQi_m : ∑ k ∈ T, Q i k = 1) (hQj_m : ∑ k ∈ T, Q j k = 1)
--       (hov : δ ≤ ∑ k ∈ T, min (Q i k) (Q j k))
--       (hband : ∀ k ∈ T, lo ≤ u k ∧ u k ≤ lo + W) (hW : 0 ≤ W)
--       (hηi : |u i - ∑ k ∈ T, Q i k * u k| ≤ η)
--       (hηj : |u j - ∑ k ∈ T, Q j k * u k| ≤ η) :
--       |u i - u j| ≤ (1 - δ) * W + 2 * η
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/BlockContract.lean#L19. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: the pairwise oscillation contraction

The core contraction step: two points `i, j` whose (iterated) transition laws `Q i ·`, `Q j ·` overlap
by `≥ δ` over a common support `T`, and which are each `η`-approximately `Q`-harmonic, satisfy
`|u i − u j| ≤ (1−δ)·W + 2η`, where `W` bounds the oscillation of `u` on `T` (via a band `[lo, lo+W]`).
This is the deterministic heart of the renewal oscillation contraction; the `δ` comes from the
finite-time Doeblin overlap (the remaining hard analytic input).  Opus-authored.
-/

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.pair_contract {u : ℕ → ℝ} {Q : ℕ → ℕ → ℝ} {i j : ℕ} {T : Finset ℕ} {δ η lo W : ℝ}
    (hQi_m : ∑ k ∈ T, Q i k = 1) (hQj_m : ∑ k ∈ T, Q j k = 1)
    (hov : δ ≤ ∑ k ∈ T, min (Q i k) (Q j k))
    (hband : ∀ k ∈ T, lo ≤ u k ∧ u k ≤ lo + W) (hW : 0 ≤ W)
    (hηi : |u i - ∑ k ∈ T, Q i k * u k| ≤ η)
    (hηj : |u j - ∑ k ∈ T, Q j k * u k| ≤ η) :
    |u i - u j| ≤ (1 - δ) * W + 2 * η := by sorry
