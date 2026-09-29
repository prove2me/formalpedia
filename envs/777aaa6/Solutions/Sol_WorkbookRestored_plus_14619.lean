-- Prove2me | solution 1 for WorkbookRestored.plus_14619
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:50.056569+00:00
-- url     : https://prove2.me/submissions/39799947-a45e-4894-8cdd-425b2ed2045f

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_14619. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic
open Polynomial
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (p q : Polynomial ℝ) (h : ∀ x, p.eval x = q.eval x) : p = q   := by
  nontriviality ℝ
  apply Polynomial.funext <;> simp [h]
#print axioms solution
