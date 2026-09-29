-- Prove2me | solution 1 for WorkbookRestored.plus_62454
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:02:41.143915+00:00
-- url     : https://prove2.me/submissions/eac53fac-1b6e-4cb7-9fd0-6538c369d31b

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_62454.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : 77 ^ 10 ≥ 2 ^ 10 * (10!) ^ 2   := by
  norm_num [Nat.factorial]
#print axioms solution
