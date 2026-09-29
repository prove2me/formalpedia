-- Prove2me | solution 1 for WorkbookRestored.plus_25423
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:01:48.836237+00:00
-- url     : https://prove2.me/submissions/db076320-05ff-41b1-831c-ff0882e36ef7

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_25423.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℝ) : tan x ^ 4 + tan y ^ 4 ≥ 2 * tan x ^ 2 * tan y ^ 2   := by
  nlinarith [sq_nonneg (tan x ^ 2 - tan y ^ 2), sq_nonneg (tan x ^ 2 + tan y ^ 2)]
#print axioms solution
