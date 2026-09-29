-- Prove2me | solution 1 for WorkbookRestored.plus_38834
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:37:12.975759+00:00
-- url     : https://prove2.me/submissions/514101c4-8b4a-4137-bd36-503b7555082f

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_38834.
   Import/namespace repair; mathematical statement unchanged. -/
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n k : ℕ) (h₀ : k ≤ n) : choose n k ≤ choose n (n/2)   := by
  exact Nat.choose_le_middle k n
#print axioms solution
