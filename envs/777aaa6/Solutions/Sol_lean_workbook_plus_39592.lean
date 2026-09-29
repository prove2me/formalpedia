-- Prove2me | solution 1 for lean_workbook_plus_39592
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-03-15T15:08:55.22178+00:00
-- url     : https://prove2.me/submissions/4fe8036d-e0d4-4735-a76a-0b3ea3b05bd8

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

theorem solution (a b : ℝ)
  (h₀ : 0 ≤ a ∧ 0 ≤ b)
  (h₁ : a^2 + b^2 = a * b) :
  a = b := by
  have ha := h₀.1
  have hb := h₀.2
  -- 4(a² + b² - ab) = (2a - b)² + 3b² = 0
  -- So b = 0 and 2a = b = 0, hence a = b = 0
  have h1 : (2 * a - b) ^ 2 + 3 * b ^ 2 = 0 := by nlinarith
  have h2 : b = 0 := by nlinarith [sq_nonneg (2 * a - b)]
  have h3 : a = 0 := by nlinarith [sq_nonneg (2 * a - b)]
  linarith

-- Auto-generated type check: solution must match the target
theorem _type_check_target  (a b : ℝ)
  (h₀ : 0 ≤ a ∧ 0 ≤ b)
  (h₁ : a^2 + b^2 = a * b) :
  a = b   := by apply solution; repeat assumption
