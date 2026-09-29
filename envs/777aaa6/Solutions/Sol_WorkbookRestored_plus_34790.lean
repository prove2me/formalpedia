-- Prove2me | solution 1 for WorkbookRestored.plus_34790
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:37:10.069357+00:00
-- url     : https://prove2.me/submissions/dfbed2c3-801e-498b-8e80-84cf4d9a7de3

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_34790.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∃ A : Matrix (Fin 2) (Fin 2) ℤ, A.det ≠ 0   := by
  exact ⟨1, by simp⟩
#print axioms solution
