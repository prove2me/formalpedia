-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
-- name    : AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:44:07.825388+00:00
-- url     : https://prove2.me/theorems/1bd9c4c5-13c3-4ab6-b644-0f0cdccf9209
-- title:
--   Sigma Recurrence mathematical objects
-- statement:
--   For a natural number $m$, `sigmaR m` is the real number $\sigma_1(m)=\sum_{d\mid m} d$, the divisor sum `ArithmeticFunction.sigma 1 m` cast to $\mathbb R$.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/SigmaRecurrence.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

open scoped BigOperators

noncomputable def sigmaR (m : ℕ) : ℝ :=
  (ArithmeticFunction.sigma 1 m : ℝ)

end AnalyticCombinatorics.Ch8.Partitions.Sigma


