-- Prove2me | solution 1 for WorkbookRestored.plus_33584
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:04:44.069137+00:00
-- url     : https://prove2.me/submissions/a26f2def-dd01-459d-b166-6a3209829a04

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_33584.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (n : ℕ)
  (h₀ : 0 < n) :
  ((Complex.exp (2 * π * Complex.I / n))^n - 1) = 0   := by
  rw [← Complex.exp_nat_mul, mul_comm]
  field_simp [h₀.ne']
  simp [Complex.exp_two_pi_mul_I]
#print axioms solution
