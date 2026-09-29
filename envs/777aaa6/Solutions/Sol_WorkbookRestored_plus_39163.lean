-- Prove2me | solution 1 for WorkbookRestored.plus_39163
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:37:14.447799+00:00
-- url     : https://prove2.me/submissions/998ebb56-c8ff-47ba-8354-27607e177d9e

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_39163.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n p : ℕ) : fib (n + p + 1) = fib (n + 1) * fib (p + 1) + fib n * fib p   := by
  simpa [add_comm, add_left_comm, add_assoc] using Nat.fib_add n p
#print axioms solution
