-- Prove2me | solution 1 for WorkbookSyntax.plus_68270
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:14:59.492348+00:00
-- url     : https://prove2.me/submissions/af60075f-9938-4c55-aaac-4dafbb1567e7

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_68270.
   The obsolete finite binder is changed from in to ∈; ranges, casts, quantifiers and mathematical expressions are unchanged. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∑ k ∈ Finset.Icc 1 4, k = 10   := by
  decide +kernel
#print axioms solution
