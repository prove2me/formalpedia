-- Prove2me | solution 1 for WorkbookRestored.plus_66159
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:15:08.845778+00:00
-- url     : https://prove2.me/submissions/97657f0f-a1ac-4624-b85d-3c8e2791db0f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_66159.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b c r : ℝ) : (a^r + b^r - c^r)*(a - b)^2 + (b^r + c^r - a^r)*(b - c)^2 + (c^r + a^r - b^r)*(c - a)^2 = 2*(a^r*(a - b)*(a - c) + b^r*(b - c)*(b - a) + c^r*(c - a)*(c - b))   := by
  ring
#print axioms solution
