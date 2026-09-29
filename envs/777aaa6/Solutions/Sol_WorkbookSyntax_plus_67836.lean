-- Prove2me | solution 1 for WorkbookSyntax.plus_67836
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:14:58.726987+00:00
-- url     : https://prove2.me/submissions/f6ff67e8-ea7e-4aef-8dac-6dfcdfca7886

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_67836.
   The obsolete finite binder is changed from in to ∈; ranges, casts, quantifiers and mathematical expressions are unchanged. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∑ i ∈ Finset.Icc 1 2019, Nat.gcd i (2019 - i) = 6725   := by
  decide +kernel
#print axioms solution
