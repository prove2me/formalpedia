-- Prove2me | solution 1 for WorkbookRestored.plus_61852
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:25:10.085991+00:00
-- url     : https://prove2.me/submissions/9a30bbeb-0af8-41ca-ba02-325bddf8c249

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_61852.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : 1 / Real.cos (π / 3) = 2   := by
  norm_num [cos_pi_div_three]
#print axioms solution
