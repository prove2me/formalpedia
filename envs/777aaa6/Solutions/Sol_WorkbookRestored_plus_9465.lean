-- Prove2me | solution 1 for WorkbookRestored.plus_9465
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:46:29.726026+00:00
-- url     : https://prove2.me/submissions/8b7d0bd8-736b-43ad-a091-1df79a44843f

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_9465.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) : choose (n + 2) 4 = choose n 2 + 2 * choose n 3 + choose n 4   := by
  simp [choose_succ_succ, add_comm, add_left_comm, add_assoc]
  ring
#print axioms solution
