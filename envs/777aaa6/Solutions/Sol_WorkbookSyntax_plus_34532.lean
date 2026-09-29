-- Prove2me | solution 1 for WorkbookSyntax.plus_34532
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:07:03.555989+00:00
-- url     : https://prove2.me/submissions/f23fc31c-5c8a-4887-84f2-8c95a40941db

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_34532.
   Only finite binder notation and required imports/namespaces are repaired. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) : (∑ i ∈ Finset.range (n + 1), i) = n * (n + 1) / 2   := by
  simp [Finset.sum_range_id, Nat.mul_comm]
#print axioms solution
