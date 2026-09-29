-- Prove2me | solution 1 for WorkbookRestored.plus_69206
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:15:11.486468+00:00
-- url     : https://prove2.me/submissions/2bb70203-8d63-4177-8be3-56dab4d17992

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_69206.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (A B : Matrix (Fin 2) (Fin 2) ℝ) :
  (A * B - B * A).det + (A * B + B * A).det = 4 * (A * B).det   := by
  simp [Matrix.det_fin_two, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Fin.sum_univ_succ]
  ring
#print axioms solution
