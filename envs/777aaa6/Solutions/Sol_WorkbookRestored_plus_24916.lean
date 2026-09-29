-- Prove2me | solution 1 for WorkbookRestored.plus_24916
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:55.729043+00:00
-- url     : https://prove2.me/submissions/1b7eadf7-2ee5-444c-ae70-ffd4ab8c1c14

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_24916. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (y : ℝ) (hy : 1 ≤ y) : y ^ (y - 1) ≥ 1   := by
  exact one_le_rpow (by linarith) (by linarith)
#print axioms solution
