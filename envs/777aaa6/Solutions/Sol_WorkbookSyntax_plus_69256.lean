-- Prove2me | solution 1 for WorkbookSyntax.plus_69256
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:15:01.162985+00:00
-- url     : https://prove2.me/submissions/abe64f24-9289-4d2d-8ff1-8b9a00d6e09c

/- Source: internlm/Lean-Workbook, Apache-2.0, row lean_workbook_plus_69256.
   The obsolete finite binder is changed from in to ∈; ranges, casts, quantifiers and mathematical expressions are unchanged. -/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n m : ℕ) : ∑ k ∈ Finset.range (m+1), choose (n + k) k = choose (n + m + 1) m   := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    simpa only [Nat.add_assoc, Nat.succ_eq_add_one] using (Nat.choose_succ_succ (n + m + 1) m).symm
#print axioms solution
