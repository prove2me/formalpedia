-- Prove2me | solution 1 for WorkbookRestored.plus_78499
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:44:51.016861+00:00
-- url     : https://prove2.me/submissions/9f4bfb90-c37e-4f52-9ff5-9659765c3ab4

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_78499.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (f : ℕ → ℕ) (f_def : ∀ n, f n = n - 10 * Nat.floor (n / 10)) : f 0! + f 1! + f 2! + f 3! + f 4! = 14   := by
  norm_num [f_def, Nat.factorial, Nat.floor_nat]
#print axioms solution
