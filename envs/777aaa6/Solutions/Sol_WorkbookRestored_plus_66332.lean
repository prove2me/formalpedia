-- Prove2me | solution 1 for WorkbookRestored.plus_66332
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:15.867154+00:00
-- url     : https://prove2.me/submissions/3d8e8f60-dedb-4b22-8032-a6df1aa3ef11

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_66332.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (x a b : ℝ)
  (h₀ : a > 0 ∧ b > 0)
  (h₁ : a ≠ 1 ∧ b ≠ 1)
  (h₂ : x ≠ 0) :
  (x * Real.log a + Real.log (1 + 1 / a^x)) / (x * Real.log b + Real.log (1 + 1 / b^x))
    = (Real.log a + 1 / x * Real.log (1 + 1 / a^x)) / (Real.log b + 1 / x * Real.log (1 + 1 / b^x))   := by
  field_simp [h₀.1,h₀.2,h₁.1,h₁.2,h₂]
#print axioms solution
