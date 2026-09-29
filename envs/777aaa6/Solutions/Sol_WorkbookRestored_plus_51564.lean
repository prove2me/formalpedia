-- Prove2me | solution 1 for WorkbookRestored.plus_51564
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:47.043149+00:00
-- url     : https://prove2.me/submissions/23ace3f5-b5a4-42f1-8606-2ad16a3d3ed5

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_51564.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution : ∀ n : ℕ, choose n 0 = 1   := by
  exact Nat.choose_zero_right
#print axioms solution
