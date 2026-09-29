-- Prove2me | solution 1 for WorkbookSyntax.plus_67809
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:14:58.000994+00:00
-- url     : https://prove2.me/submissions/fed339cf-f619-4a19-9c40-ccc43aedfcf1

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_67809.
   The obsolete finite binder is changed from in to ∈; ranges, casts, quantifiers and mathematical expressions are unchanged. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) : ∑ k ∈ Finset.Icc 3 51, (Nat.choose k 3 * Nat.choose (52 - k) 1) = Nat.choose 53 5   := by
  decide +kernel
#print axioms solution
