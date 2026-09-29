-- Prove2me | solution 1 for WorkbookRestored.plus_2271
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:59:04.536444+00:00
-- url     : https://prove2.me/submissions/4d9d9e4b-86d0-487a-82c2-9313c064f350

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_2271.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (x y : ℂ) : Matrix.det (![![y, x, x+y],![x+y, y, x],![x, x+y, y]]) = 2 * (x^3 + y^3)   := by
  simp [Matrix.det_fin_three]
  ring
#print axioms solution
