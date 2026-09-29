-- Prove2me | solution 1 for WorkbookRestored.plus_9802
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:46:30.620299+00:00
-- url     : https://prove2.me/submissions/449430fe-94f9-4b7e-add5-cd80b0b0b551

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_9802.
   The proposition is unchanged; missing imports/namespaces are restored. -/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) : fib n ^ 2 + fib (n + 1) ^ 2 = fib (2 * n + 1)   := by
  simp [fib_add_two, fib_two_mul, fib_two_mul_add_one]
  ring
#print axioms solution
