-- Prove2me | solution 1 for WorkbookRestored.plus_52753
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:49:29.105334+00:00
-- url     : https://prove2.me/submissions/bfd9e0d9-a57a-494d-a5f3-79d16107bc01

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_52753.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) (h : n ≠ 0) : choose n (n-1) = n   := by
  simpa using (Nat.choose_symm (show 1 ≤ n by omega))
#print axioms solution
