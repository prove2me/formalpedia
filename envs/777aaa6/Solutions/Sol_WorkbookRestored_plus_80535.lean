-- Prove2me | solution 1 for WorkbookRestored.plus_80535
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:35.254753+00:00
-- url     : https://prove2.me/submissions/5e453a54-ca07-4530-8ae0-20344e01d788

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_80535.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (b : ℝ) : ∃ r_b, sin r_b = 1 / Real.sqrt (1 + b^2)   := by
  refine ⟨arcsin (1 / sqrt (1 + b^2)), ?_⟩
  apply sin_arcsin
  · have h : (0:ℝ) ≤ 1 / sqrt (1 + b^2) := by positivity
    linarith
  · have h : (1:ℝ) ≤ sqrt (1 + b^2) := by
      apply le_sqrt_of_sq_le
      nlinarith [sq_nonneg b]
    exact (div_le_one (by positivity : (0:ℝ)<sqrt (1+b^2))).2 h
#print axioms solution
