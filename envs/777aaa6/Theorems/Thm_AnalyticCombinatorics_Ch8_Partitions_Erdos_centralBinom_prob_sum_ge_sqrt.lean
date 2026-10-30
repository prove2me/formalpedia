-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_centralBinom_prob_sum_ge_sqrt
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.centralBinom_prob_sum_ge_sqrt
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:30:47.592691+00:00
-- url     : https://prove2.me/theorems/e46b6121-19f5-498f-bb83-9e4ea8def27c
-- title:
--   A lower bound for central-binomial probability sums
-- statement:
--   For every natural number $N$, including zero, put $q_m=\binom{2m}{m}/4^m$. Then $$\sqrt N\le\sum_{m=0}^{N-1}q_m.$$ This is a finite-sum lower bound.
--
--   The local source models, scales or predicates are defined exactly by:
--
--   ```lean
--   noncomputable def cbProb (m : ℕ) : ℝ := (Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/CentralBinomSum.lean#L121. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_CentralBinomSum
import Mathlib.Data.Nat.Choose.Central
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Central-binomial Green sum: `√N ≤ ∑_{m<N} C_m / 4^m` (renewal route B, SRW Green helper)

The lazy/simple-random-walk Green local time over a horizon `N` is `∑_{m<N} a_m` with
`a_m = binom(2m,m)/4^m = Nat.centralBinom m / 4^m` the return probability.  The block-heat
lower bound `greenT_lower_fixed_window` consumes the fact that this partial sum grows like `√N`;
this file banks the clean, fully elementary lower bound

  `√N ≤ ∑_{m<N} Nat.centralBinom m / 4^m`,

with the *exact* constant `1`, via the term bound `1/√(4m+1) ≤ a_m` and the telescope
`√(m+1) − √m ≤ 1/√(4m+1)`.  No Stirling, Wallis, generating functions or integral estimates.
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.centralBinom_prob_sum_ge_sqrt (N : ℕ) :
    Real.sqrt (N : ℝ) ≤ ∑ m ∈ Finset.range N, cbProb m := by sorry
