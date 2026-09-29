-- Prove2me | solution 1 for WorkbookRestored.plus_50816
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:45.551984+00:00
-- url     : https://prove2.me/submissions/6f760008-f0bf-4806-8112-50d67c56ae20

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_50816.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b c : ℝ) :
  Matrix.det (![![a, b, c],![c, a, b],![b, c, a]]) = a^3 + b^3 + c^3 - 3*a*b*c   := by
  simp [Matrix.det_fin_three]
  ring
#print axioms solution
