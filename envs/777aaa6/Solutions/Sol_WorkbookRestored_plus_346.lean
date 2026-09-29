-- Prove2me | solution 1 for WorkbookRestored.plus_346
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:17:36.619974+00:00
-- url     : https://prove2.me/submissions/e40f99ad-046f-43cd-b975-ea28068c4615

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_346.
   Draft repair: only required imports and namespaces are restored. -/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (n k m : ℕ) (h₁ : k ≤ n) (h₂ : m ≤ k) : choose n k * choose k m = choose n m * choose (n - m) (k - m)   := by
  simp [choose_mul, h₁, h₂, sub_eq_iff_eq_add]
#print axioms solution
