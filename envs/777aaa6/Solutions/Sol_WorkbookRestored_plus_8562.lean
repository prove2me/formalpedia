-- Prove2me | solution 1 for WorkbookRestored.plus_8562
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:46:27.830298+00:00
-- url     : https://prove2.me/submissions/ac4d3224-d6af-4947-b31d-6e47aa2eb448

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_8562.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a x y : ℝ) (ha : 0 < a) : a^x * a^y = a^(x + y)   := by
  simp [← Real.rpow_add ha]
#print axioms solution
