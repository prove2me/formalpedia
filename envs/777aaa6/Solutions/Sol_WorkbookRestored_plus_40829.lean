-- Prove2me | solution 1 for WorkbookRestored.plus_40829
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:41:41.432457+00:00
-- url     : https://prove2.me/submissions/58ce7ff1-baa2-475b-895a-a0d850e6439f

/- InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_40829. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
open Nat
set_option autoImplicit false
theorem solution (n j : ℕ) (h₁ : 2 * j + 1 > n) : choose n (2 * j + 1) = 0   := by
  rw [Nat.choose_eq_zero_of_lt h₁]
#print axioms solution
