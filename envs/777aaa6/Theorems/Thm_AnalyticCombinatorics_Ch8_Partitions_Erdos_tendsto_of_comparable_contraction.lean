-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_tendsto_of_comparable_contraction
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.tendsto_of_comparable_contraction
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:48:21.393805+00:00
-- url     : https://prove2.me/theorems/2e4ef18d-f256-4ebe-b70a-cd7011f1d318
-- title:
--   Convergence from comparable contraction and carried summability
-- statement:
--   Abstract center-tracking convergence packaging with summability carried; no construction of partition center links.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem tendsto_of_comparable_contraction {h c V : ℕ → ℝ} {rank : ℕ → ℕ}
--       (hrank : Tendsto rank atTop atTop)
--       (hVtend : Tendsto V atTop (𝓝 0))
--       (hVsum : Summable V)
--       (htrack : ∀ n, |h n - c (rank n)| ≤ V (rank n))
--       (hlink : ∀ R, |c (R + 1) - c R| ≤ V R) :
--       ∃ L : ℝ, Tendsto h atTop (𝓝 L)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/CompContraction.lean#L21. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: comparable-pair contraction ⟹ convergence (center-tracking packaging)

The far-pair obstruction is resolved by center-tracking: it suffices to control *comparable*-rank
oscillation (block centers `c` and a block-oscillation bound `V`), with far pairs handled by the
summable center links.  This lemma packages `tendsto_of_center_tracking` into the form produced by the
windowed-coupling ITER: a summable block-oscillation bound `V → 0` with `|h n − c(rank n)| ≤ V(rank n)`
(tracking) and adjacent centers `|c(R+1) − c R| ≤ V R` forces `h` to converge.  Opus-authored.
-/

open Filter Topology

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.tendsto_of_comparable_contraction {h c V : ℕ → ℝ} {rank : ℕ → ℕ}
    (hrank : Tendsto rank atTop atTop)
    (hVtend : Tendsto V atTop (𝓝 0))
    (hVsum : Summable V)
    (htrack : ∀ n, |h n - c (rank n)| ≤ V (rank n))
    (hlink : ∀ R, |c (R + 1) - c R| ≤ V R) :
    ∃ L : ℝ, Tendsto h atTop (𝓝 L) := by sorry
