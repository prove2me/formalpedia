-- Prove2me | Theorems.Thm_cdfVariance_nonneg
-- name    : cdfVariance_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:49:19.060895+00:00
-- url     : https://prove2.me/theorems/c7788ab2-e15a-48bc-961c-ffcb97ea7210
-- title:
--   Chapter 1, def_1_3: cdfVariance_nonneg
-- statement:
--   Source theorem `cdfVariance_nonneg` from Chapter 1, module `def_1_3`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F000
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section

theorem cdfVariance_nonneg (a b : ℝ) (F : ℝ → ℝ)
    (h_int_exp : RSIntegrable (fun x => x) F a b)
    (h_int_var : RSIntegrable (fun x => (x - cdfExpectation a b F h_int_exp)^2) F a b) :
    0 ≤ cdfVariance a b F h_int_exp h_int_var := by sorry

end   

noncomputable section DiscreteExpectation

namespace DiscreteExpectation

end DiscreteExpectation   
end DiscreteExpectation   

section ContinuousExpectation

namespace ContinuousExpectation

end ContinuousExpectation   
end ContinuousExpectation
