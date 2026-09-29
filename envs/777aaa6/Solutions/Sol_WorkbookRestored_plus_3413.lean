-- Prove2me | solution 1 for WorkbookRestored.plus_3413
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:46:24.539357+00:00
-- url     : https://prove2.me/submissions/f1776f96-9dd9-43d6-a26f-03eb07b6dfcc

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_3413.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ x : ℕ, choose x 2 = (x^2 - x) / 2   := by
  refine' fun x => (Nat.choose_two_right x).trans _
  simp [sq, tsub_mul, mul_tsub, mul_comm, mul_assoc, mul_left_comm]
#print axioms solution
