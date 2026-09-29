-- Prove2me | solution 1 for WorkbookRestored.plus_34252
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:37:08.441567+00:00
-- url     : https://prove2.me/submissions/aa6ef4e1-d664-4a04-92d3-fc925e0cdc67

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_34252.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : 9! ≡ -1 [ZMOD 71]   := by
  norm_num [Nat.factorial, Int.ModEq]
#print axioms solution
