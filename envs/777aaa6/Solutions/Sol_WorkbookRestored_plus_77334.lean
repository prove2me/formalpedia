-- Prove2me | solution 1 for WorkbookRestored.plus_77334
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:44:48.746473+00:00
-- url     : https://prove2.me/submissions/0e68abcd-7554-4d6f-ac15-a0e4f2bee3fc

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_77334.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n : ℕ) (h : n = 15) : φ n = 8   := by
  subst n
  decide +kernel
#print axioms solution
