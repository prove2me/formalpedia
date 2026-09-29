-- Prove2me | solution 1 for WorkbookRestored.plus_51287
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:46.320852+00:00
-- url     : https://prove2.me/submissions/e04a76f5-b847-41d7-911c-c828b563c27f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_51287.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n m : ℕ) (hn : n ∣ m) : fib n ∣ fib m   := by
  exact Nat.fib_dvd n m hn
#print axioms solution
