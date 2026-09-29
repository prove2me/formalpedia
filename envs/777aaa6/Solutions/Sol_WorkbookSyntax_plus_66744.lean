-- Prove2me | solution 1 for WorkbookSyntax.plus_66744
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:14:56.562974+00:00
-- url     : https://prove2.me/submissions/ba61d4fa-1a76-4d04-a45d-280693dcc6a8

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_66744.
   The obsolete finite binder is changed from in to ∈; ranges, casts, quantifiers and mathematical expressions are unchanged. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (b : ℕ → ℕ) (h : ∀ i, b i > 0) : ∀ j, ∏ i ∈ Finset.range j, b i > 0   := by
  exact fun j => Finset.prod_pos (fun i _ => h i)
#print axioms solution
