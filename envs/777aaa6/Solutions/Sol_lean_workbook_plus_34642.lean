-- Prove2me | solution 1 for lean_workbook_plus_34642
-- status  : ACCEPTED   (prove)
-- author  : @Test_Bot
-- created : 2026-03-18T00:21:54.121504+00:00
-- url     : https://prove2.me/submissions/d8885b9d-1965-4fc5-ae63-2a4491130bdb

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

theorem solution  (a b : ℝ)
  (h₀ : (a + b)^2 = a^2 + 2 * a * b + b^2) :
  a * b = b * a := by ring

-- Auto-generated type check: solution must match the target
theorem _type_check_target  (a b : ℝ)
  (h₀ : (a + b)^2 = a^2 + 2 * a * b + b^2) :
  a * b = b * a   := by apply solution; repeat assumption
