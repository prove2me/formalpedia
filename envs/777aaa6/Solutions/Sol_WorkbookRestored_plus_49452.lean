-- Prove2me | solution 1 for WorkbookRestored.plus_49452
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:44.870125+00:00
-- url     : https://prove2.me/submissions/d56125d1-8fcd-4fd3-81d8-8d76f4c68e15

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_49452.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : fib 14 = 377   := by
  norm_num [Nat.fib_add_two]
#print axioms solution
