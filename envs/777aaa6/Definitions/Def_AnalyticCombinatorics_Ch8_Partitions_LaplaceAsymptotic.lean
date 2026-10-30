-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_LaplaceAsymptotic
-- name    : AnalyticCombinatorics_Ch8_Partitions_LaplaceAsymptotic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T13:49:29.875191+00:00
-- url     : https://prove2.me/theorems/7878e956-50c3-45b5-b313-4499cc02d01f
-- title:
--   Laplace Asymptotic mathematical objects
-- statement:
--   For any real t, PartLaplace(t) is the totalized infinite sum of part(n) exp(-t n) over all natural n. The definition itself imposes no convergence hypothesis; interpreting it as a convergent Laplace transform requires a separate summability result.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/LaplaceAsymptotic.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


namespace AnalyticCombinatorics.Ch8.Partitions

open Filter
open scoped BigOperators Topology

noncomputable def PartLaplace (t : ℝ) : ℝ :=
  ∑' n : ℕ, part n * Real.exp (-(t * n))

end AnalyticCombinatorics.Ch8.Partitions


