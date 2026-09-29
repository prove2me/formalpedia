-- Prove2me | solution 1 for WorkbookRestored.plus_71078
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:45.648949+00:00
-- url     : https://prove2.me/submissions/3d5a8100-24e8-4322-bfe2-6e13538235a3

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_71078.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (P : Polynomial ℝ) (hP : ∀ n, P.coeff n ≤ 0) (x : ℝ) (hx : 0 ≤ x) : P.eval x ≤ 0   := by
  rw [Polynomial.eval_eq_sum_range]
  exact Finset.sum_nonpos fun n _ => mul_nonpos_of_nonpos_of_nonneg (hP n) (pow_nonneg hx n)
#print axioms solution
