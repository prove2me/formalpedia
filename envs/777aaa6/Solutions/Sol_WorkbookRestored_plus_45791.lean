-- Prove2me | solution 1 for WorkbookRestored.plus_45791
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:44.187018+00:00
-- url     : https://prove2.me/submissions/20e2e7ff-6947-4fa0-b911-1273206723c5

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_45791.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (X : Type*) [AddCommGroup X] [Module ℝ X]
    (Y : Submodule ℝ X) : Module.rank ℝ Y + Module.rank ℝ (X ⧸ Y) = Module.rank ℝ X   := by
  simpa [add_comm] using rank_quotient_add_rank_of_divisionRing Y
#print axioms solution
