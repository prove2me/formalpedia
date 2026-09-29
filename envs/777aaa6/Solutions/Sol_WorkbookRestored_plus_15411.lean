-- Prove2me | solution 1 for WorkbookRestored.plus_15411
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:51.033995+00:00
-- url     : https://prove2.me/submissions/cf5c3b65-8b05-43e3-8d4d-21a6327c53f4

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_15411. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (a b c : ℝ) : Matrix.det (![![a+b, b+c, c+a],![a^2+b^2, b^2+c^2, c^2+a^2],![a^3+b^3, b^3+c^3, c^3+a^3]]) = 2*a*b*c*(a-b)*(b-c)*(c-a)   := by
  simp [Matrix.det_fin_three]
  ring
#print axioms solution
