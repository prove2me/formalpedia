-- Prove2me | solution 1 for WorkbookRestored.plus_72890
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:47.971833+00:00
-- url     : https://prove2.me/submissions/9eda3993-f073-42aa-a626-23dbf71f13a8

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_72890.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : 15! % 1000 = 0   := by
  decide +kernel
#print axioms solution
