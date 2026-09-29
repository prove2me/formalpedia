-- Prove2me | solution 1 for lean_workbook_plus_38082
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:43.6903+00:00
-- url     : https://prove2.me/submissions/719b1a0a-6ec1-4cec-8ce1-bf3c45683f1d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ) (hab : 0 ≤ a ∧ 0 ≤ b ∧ a ≤ b ∧ b ≤ 1) :
  0 ≤ a / (b + 1) + b / (a + 1) ∧ a / (b + 1) + b / (a + 1) ≤ 1 := by
  rcases hab with ⟨ha,hb,hab,hb1⟩
  have ha1 : 0 ≤ 1+a := by linarith
  have hb1' : 0 ≤ 1+b := by linarith
  constructor
  · positivity
  · have hi : 1-(a/(b+1)+b/(a+1)) = ((1-b)*(1+b)+a*(b-a))/((a+1)*(b+1)) := by
      field_simp
      ring
    have hn : 0 ≤ ((1-b)*(1+b)+a*(b-a))/((a+1)*(b+1)) := by
      apply div_nonneg
      · exact add_nonneg (mul_nonneg (by linarith) hb1') (mul_nonneg ha (by linarith))
      · positivity
    linarith
