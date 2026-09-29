-- Prove2me | solution 1 for WorkbookRestored.plus_54222
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:49:31.441536+00:00
-- url     : https://prove2.me/submissions/3f010715-3867-4d61-a7c2-1b055a83fd9b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_54222.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (f g : Polynomial ℤ) : (f * g).degree = f.degree + g.degree   := by
  exact Polynomial.degree_mul
#print axioms solution
