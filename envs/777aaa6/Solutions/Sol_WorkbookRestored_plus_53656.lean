-- Prove2me | solution 1 for WorkbookRestored.plus_53656
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:49:30.609439+00:00
-- url     : https://prove2.me/submissions/4f7138df-9237-45a8-8cb4-ce68890a8e37

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_53656.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b c : ℝ) : Matrix.det (![![-2*a, a+b, c+a],![a+b, -2*b, b+c],![c+a, b+c, -2*c]]) = 4*(a+b)*(b+c)*(c+a)   := by
  simp [Matrix.det_fin_three]
  ring
#print axioms solution
