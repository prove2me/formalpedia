-- Prove2me | solution 1 for WorkbookSyntax.plus_68935
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:15:00.390734+00:00
-- url     : https://prove2.me/submissions/2994759e-08fd-440c-9046-e2069d414e57

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_68935.
   The obsolete finite binder is changed from in to ∈; ranges, casts, quantifiers and mathematical expressions are unchanged. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
  ∑ k ∈ (Finset.Icc 1 99), (k * (k + 1)) = 333300   := by
  decide +kernel
#print axioms solution
