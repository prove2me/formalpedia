-- Prove2me | solution 1 for WorkbookRestored.plus_10295
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:46:32.251347+00:00
-- url     : https://prove2.me/submissions/14afe87a-c93f-460c-8551-0a8a17c28ec8

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_10295.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n k : ℕ) : choose (n - 1 + k) (n - 1) = choose (n - 1 + k) k   := by
  rw [add_comm, choose_symm_add]
#print axioms solution
