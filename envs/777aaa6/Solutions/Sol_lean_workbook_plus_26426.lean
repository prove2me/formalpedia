-- Prove2me | solution 1 for lean_workbook_plus_26426
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:39.19588+00:00
-- url     : https://prove2.me/submissions/37e9f20b-58b7-4526-a359-f996bda19daf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a^4 + b^4 + c^4 + a^2 * b^2 + a^2 * c^2 + b^2 * c^2 ≥ a^3 * b + b^3 * c + c^3 * a + a * b^2 * c + a * b * c^2 + a^2 * b * c := by
  intro a b c
  intros
  have h : (0 : ℝ) ≤ (a^4 + b^4 + c^4 + a^2 * b^2 + a^2 * c^2 + b^2 * c^2) - (a^3 * b + b^3 * c + c^3 * a + a * b^2 * c + a * b * c^2 + a^2 * b * c) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((c ^ 2) + ((-1) * a * c)))^2 + ((1 / 2) : ℝ) * (((c ^ 2) + ((-1) * a * b)))^2 + ((1 / 2) : ℝ) * ((((-1) * (b ^ 2)) + (b * c)))^2 + ((1 / 2) : ℝ) * ((((-1) * (a ^ 2)) + (b * c)))^2 + ((1 / 2) : ℝ) * (((b ^ 2) + ((-1) * a * c)))^2 + ((1 / 2) : ℝ) * ((((-1) * (a ^ 2)) + (a * b)))^2 := by positivity
      _ = (a^4 + b^4 + c^4 + a^2 * b^2 + a^2 * c^2 + b^2 * c^2) - (a^3 * b + b^3 * c + c^3 * a + a * b^2 * c + a * b * c^2 + a^2 * b * c) := by ring
  exact sub_nonneg.mp h
