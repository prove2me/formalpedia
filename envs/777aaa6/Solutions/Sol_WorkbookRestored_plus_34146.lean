-- Prove2me | solution 1 for WorkbookRestored.plus_34146
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:46.775419+00:00
-- url     : https://prove2.me/submissions/69f64598-bff7-4940-ac01-344a04afd188

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_34146.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) (h₁ : 1 < x) (h₂ : 1 < y) (h₃ : x < y) : (x - 1) * Real.log x < (y - 1) * Real.log y   := by
  have h₄ : 0 < Real.log x := Real.log_pos (by linarith)
  have h₅ : 0 < Real.log y := Real.log_pos h₂
  have h₆ : 0 < x - 1 := by linarith
  gcongr
#print axioms solution
