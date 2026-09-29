-- Prove2me | solution 1 for WorkbookRestored.plus_71937
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:46.738659+00:00
-- url     : https://prove2.me/submissions/d94db181-0f6a-48de-b5bf-1ccede3628f4

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_71937.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (f : ℕ → ℚ) (f_def : f 0 = 1 ∧ ∀ x, 1 ≤ x → f x = (f (x - 1) + 1) / (x + 1)) : (0! + 1! + 2! + 3! + 4! + 5! + 6! + 7!) / f 7 = 8!   := by
  norm_num [Nat.factorial_succ, f_def.1, f_def.2]
#print axioms solution
