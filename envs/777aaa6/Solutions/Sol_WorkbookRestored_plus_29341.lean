-- Prove2me | solution 1 for WorkbookRestored.plus_29341
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:57.839323+00:00
-- url     : https://prove2.me/submissions/7f677bda-263e-4078-b367-c506a9207305

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_29341. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic
open Polynomial
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (P : Polynomial ℤ) {a b : ℤ} (h : a ≠ b) : a - b ∣ P.eval a - P.eval b   := by
  exact Polynomial.sub_dvd_eval_sub a b P
#print axioms solution
