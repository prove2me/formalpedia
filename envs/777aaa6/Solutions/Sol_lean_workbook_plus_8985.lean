-- Prove2me | solution 1 for lean_workbook_plus_8985
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:35.774943+00:00
-- url     : https://prove2.me/submissions/69e0895b-3088-47b2-98de-ba530ce87884

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (hab : 0 ≤ a ∧ 0 ≤ b) (habp : a * b + a + b = 3) : 4 ≤ a * b * (a ^ 2 + b ^ 2) + a ^ 3 + b ^ 3 ∧ a * b * (a ^ 2 + b ^ 2) + a ^ 3 + b ^ 3 ≤ 27 := by
  rcases hab with ⟨ha,hb⟩
  have hs0 : 0 ≤ a+b := by positivity
  have hs3 : a+b ≤ 3 := by nlinarith [mul_nonneg ha hb]
  have hs2 : 2 ≤ a+b := by
    by_contra h
    have hp := mul_nonneg (show 0 ≤ 2-a-b by linarith) hs0
    nlinarith [sq_nonneg (a-b)]
  have hid : a*b*(a^2+b^2)+a^3+b^3 = 4*(a+b)^2+3*(a+b)-18 := by
    linear_combination (a^2+b^2-a-b-6) * habp
  constructor
  · rw [hid]
    nlinarith [mul_nonneg (show 0 ≤ a+b-2 by linarith) (show 0 ≤ a+b+2 by positivity)]
  · rw [hid]
    nlinarith [mul_nonneg (show 0 ≤ 3-a-b by linarith) (show 0 ≤ 3+a+b by positivity)]
