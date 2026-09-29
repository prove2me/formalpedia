-- Prove2me | solution 1 for WorkbookRestored.plus_54971
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:49:32.133214+00:00
-- url     : https://prove2.me/submissions/1e187b87-89b0-4375-8a83-d9fa710c3616

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_54971.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : 18! ≡ -1 [ZMOD 437]   := by
  norm_num [Nat.factorial, Int.ModEq]
#print axioms solution
