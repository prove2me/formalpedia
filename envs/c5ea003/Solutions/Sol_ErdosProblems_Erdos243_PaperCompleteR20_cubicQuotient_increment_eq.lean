-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.cubicQuotient_increment_eq
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:01:54.947061+00:00
-- url     : https://prove2.me/submissions/a11fb898-aad6-463c-bce8-e90b0e5f44b7

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_risingCubic_ratio
import Mathlib

/-!
# Erdős 243: quotient increments at the cubic rate
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20
open Filter
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    (C : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hC : C n ≠ 0) :
    cubicQuotient C (n + 1) - cubicQuotient C n =
      cubicQuotient C n * cubicRatioError C n /
        (1 + 3 / (n : ℝ)) := by
  have hmodel := risingCubic_ratio n hn
  simp only [cubicQuotient, cubicRatioError]
  rw [hmodel]
  field_simp [risingCubic, hn.ne', hC]
