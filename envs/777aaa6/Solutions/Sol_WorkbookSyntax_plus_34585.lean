-- Prove2me | solution 1 for WorkbookSyntax.plus_34585
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:07:04.367974+00:00
-- url     : https://prove2.me/submissions/9e0a3089-bb6f-4577-8d81-90bd0c6b9750

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_34585.
   Only finite binder notation and required imports/namespaces are repaired. -/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n m : ℕ) : ∑ k ∈ Finset.range (m+1), (-1 : ℤ)^k * (2*n+1).choose k = (-1)^m * (2*n).choose m   := by
  exact Int.alternating_sum_range_choose_eq_choose
#print axioms solution
