-- Prove2me | Theorems.Thm_thm_1_4
-- name    : thm_1_4
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:12:59.644207+00:00
-- url     : https://prove2.me/theorems/178e8f2c-54ff-4228-b382-eaa26f0d1949
-- title:
--   Chapter 1, thm_1_4: thm_1_4
-- statement:
--   Source theorem `thm_1_4` from Chapter 1, module `thm_1_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators Pointwise Interval

noncomputable section

namespace Thm_1_4

end Thm_1_4

theorem thm_1_4 {f α α' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hαmono : MonotoneOn α (Icc a b))
    (hαderiv : ∀ x ∈ Icc a b, HasDerivAt α (α' x) x)
    (hα'cont : ContinuousOn α' (Icc a b))
    (hRS : RSIntegrable f α a b) :
    IntervalIntegrable (fun x => f x * α' x) volume a b ∧
      rsIntegral f α a b hRS = ∫ x in a..b, f x * α' x := by sorry
