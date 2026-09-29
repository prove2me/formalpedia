-- Prove2me | solution 1 for lean_workbook_plus_47962
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:33:39.75628+00:00
-- url     : https://prove2.me/submissions/0ea1db62-552a-4820-81de-a8a7000b14af

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : x = b * c / a^2)
  (h₂ : y = c * a / b^2)
  (h₃ : z = a * b / c^2) :
  (a + b + c)^4 ≥ a^2 * (a^2 + 26 * b * c) + b^2 * (b^2 + 26 * c * a) + c^2 * (c^2 + 26 * a * b) := by
  rcases h₀ with ⟨ha,hb,hc⟩
  clear h₁ h₂ h₃ x y z
  have h₁ : 0 ≤ c*(4*a+4*b+3*c) := by positivity
  have h₂ : 0 ≤ a*(4*b+4*c+3*a) := by positivity
  have h₃ : 0 ≤ b*(4*c+4*a+3*b) := by positivity
  nlinarith [mul_nonneg (sq_nonneg (a-b)) h₁, mul_nonneg (sq_nonneg (b-c)) h₂, mul_nonneg (sq_nonneg (c-a)) h₃]
