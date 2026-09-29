-- Prove2me | solution 1 for WorkbookRestored.plus_44804
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:05:09.56866+00:00
-- url     : https://prove2.me/submissions/edd69c59-4f30-4000-bbbe-a5edc0c6ed74

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_44804.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : Continuous fun t => (cos t, sin t)   := by
  exact continuous_cos.prodMk continuous_sin
#print axioms solution
