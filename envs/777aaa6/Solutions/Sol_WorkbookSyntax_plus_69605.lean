-- Prove2me | solution 1 for WorkbookSyntax.plus_69605
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:15:01.879983+00:00
-- url     : https://prove2.me/submissions/8ae192cb-e955-4e08-9714-fddeaeaec211

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_69605.
   The obsolete finite binder is changed from in to ∈; ranges, casts, quantifiers and mathematical expressions are unchanged. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6   := by
  intro n
  have h : 6 * (∑ i ∈ Finset.range (n + 1), i ^ 2) = n * (n + 1) * (2 * n + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.succ_eq_add_one] at *
      nlinarith [ih]
  omega
#print axioms solution
