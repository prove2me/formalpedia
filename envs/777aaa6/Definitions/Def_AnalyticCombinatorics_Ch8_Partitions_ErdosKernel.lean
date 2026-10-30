-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
-- name    : AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:46:06.729382+00:00
-- url     : https://prove2.me/theorems/5f25f2dc-a162-4247-9491-5fff6ad6e196
-- title:
--   Erdos Kernel mathematical objects
-- statement:
--   The constant C=pi sqrt(2/3) defines u(n)=n p(n)exp(-C sqrt(n)). Divisor-sum/exponential recurrence weights and a boundary term express the normalized recurrence.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ErdosKernel.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

noncomputable def C : ℝ :=
  Real.pi * Real.sqrt (2 / 3)

noncomputable def u (n : ℕ) : ℝ :=
  (n : ℝ) * Partitions.part n * Real.exp (-C * Real.sqrt (n : ℝ))

noncomputable def erdosWeight (n m : ℕ) : ℝ :=
  Sigma.sigmaR m / ((n - m : ℕ) : ℝ) *
    Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)))

noncomputable def boundaryTerm (n : ℕ) : ℝ :=
  Sigma.sigmaR n * Real.exp (-C * Real.sqrt (n : ℝ))

end

end AnalyticCombinatorics.Ch8.Partitions.Erdos


