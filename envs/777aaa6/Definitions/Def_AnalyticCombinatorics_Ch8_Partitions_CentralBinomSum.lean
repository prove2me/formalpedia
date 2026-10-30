-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_CentralBinomSum
-- name    : AnalyticCombinatorics_Ch8_Partitions_CentralBinomSum
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:29:05.125691+00:00
-- url     : https://prove2.me/theorems/4abd5ad6-2396-44fd-8e4c-73e0ec358e88
-- title:
--   Central Binom Sum
-- statement:
--   The source mathematical objects and operations are specified by the following definitions.
--
--   ```lean
--   noncomputable def cbProb (m : ℕ) : ℝ := (Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/CentralBinomSum.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The central-binomial return probability `a_m = binom(2m,m)/4^m`. -/
noncomputable def cbProb (m : ℕ) : ℝ := (Nat.centralBinom m : ℝ) / (4 : ℝ) ^ m

end AnalyticCombinatorics.Ch8.Partitions.Erdos


