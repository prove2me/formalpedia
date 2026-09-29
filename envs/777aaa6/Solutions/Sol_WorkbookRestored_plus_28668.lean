-- Prove2me | solution 1 for WorkbookRestored.plus_28668
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:56.399575+00:00
-- url     : https://prove2.me/submissions/915456e0-fd1a-423b-89e4-533dd4133485

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_28668. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic
open Polynomial
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (p q : Polynomial ℝ) (x : ℝ) :
  (p + q).derivative.eval x = p.derivative.eval x + q.derivative.eval x   := by
  simp [Polynomial.derivative_add, Polynomial.eval_add]
#print axioms solution
