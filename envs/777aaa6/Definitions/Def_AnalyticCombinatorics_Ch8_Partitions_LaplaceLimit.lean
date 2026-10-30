-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_LaplaceLimit
-- name    : AnalyticCombinatorics_Ch8_Partitions_LaplaceLimit
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T13:47:54.45393+00:00
-- url     : https://prove2.me/theorems/4faa216b-618e-47de-83c7-73bb4f11948d
-- title:
--   Laplace Limit mathematical objects
-- statement:
--   For every real t and positive natural k, logEulerTerm(t,k) = -log(1-exp(-t k)). For positive natural j as well, logBridgeTerm(t,k,j) = exp(-t k)^j/j. These are real-valued functions with no positivity assumption on t. Real.log is totalized, including log(0)=0 and its absolute-value extension on negative arguments. The definitions alone assert neither summability nor an identity between an infinite sum and the Euler product.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/LaplaceLimit.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology

-- The log bridge combines finite-product logarithms with several `tsum` reindexing steps.
set_option maxHeartbeats 800000

noncomputable def logEulerTerm (t : ℝ) (k : ℕ+) : ℝ :=
  -Real.log (1 - Real.exp (-(t * (k : ℝ))))

noncomputable def logBridgeTerm (t : ℝ) (k j : ℕ+) : ℝ :=
  Real.exp (-(t * (k : ℝ))) ^ (j : ℕ) / (j : ℝ)

end AnalyticCombinatorics.Ch8.Partitions


