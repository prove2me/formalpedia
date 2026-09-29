-- Prove2me | solution 1 for WorkbookRestored.plus_32500
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:18:58.545137+00:00
-- url     : https://prove2.me/submissions/b4c4c618-8aaa-4c54-b8f6-038698f7f551

/- Adapted from InternLM Lean-Workbook, Apache-2.0, row lean_workbook_plus_32500. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution  (x : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 9^x / (9^x + 3))
  (h₁ : 0 < x)
  (h₂ : x < 1) :
  f x + f (1 - x) = 1   := by
  have hp : 0 < (9 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x
  have hpow : (9 : ℝ) ^ (1 - x) = 9 / 9 ^ x := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
  rw [h₀ x, h₀ (1-x), hpow]
  field_simp
  <;> ring
#print axioms solution
