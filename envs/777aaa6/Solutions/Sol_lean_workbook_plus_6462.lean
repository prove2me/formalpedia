-- Prove2me | solution 1 for lean_workbook_plus_6462
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-03-15T15:09:16.680937+00:00
-- url     : https://prove2.me/submissions/b942a9dd-7524-4c3a-bd3f-8e59b8b7d6d9

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

theorem solution (a b : ℝ) (h1 : 0 ≤ a ∧ 0 ≤ b) (h2 : a ≤ b) (h3 : b ≤ 1) : a * b^2 - a^2 * b ≤ 1 / 4 := by
  have ha := h1.1
  have hb := h1.2
  -- Key: 4ab(b-a) ≤ b³ ≤ 1
  -- From AM-GM: 4a(b-a) ≤ (a + (b-a))² = b², so ab(b-a) ≤ b³/4
  -- And b ≤ 1 so b³ ≤ 1, hence ab(b-a) ≤ 1/4
  have h4 : 0 ≤ b * (b - 2 * a) ^ 2 := mul_nonneg hb (sq_nonneg _)
  have h5 : 0 ≤ (1 - b) * b ^ 2 := mul_nonneg (by linarith) (sq_nonneg b)
  nlinarith

-- Auto-generated type check: solution must match the target
theorem _type_check_target (a b : ℝ) (h1 : 0 ≤ a ∧ 0 ≤ b) (h2 : a ≤ b) (h3 : b ≤ 1) : a * b^2 - a^2 * b ≤ 1 / 4   := by apply solution; repeat assumption
