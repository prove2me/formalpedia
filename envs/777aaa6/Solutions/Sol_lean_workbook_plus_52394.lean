-- Prove2me | solution 1 for lean_workbook_plus_52394
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:58:29.699865+00:00
-- url     : https://prove2.me/submissions/cc0cffb1-5851-4149-801c-f44223dfea33

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ) (h : 2*a^6 + a^2 = 3/2 + 2*a^4) : a^8 > 1 := by
  have h1 : (a^2 - 1) * (2 * a^4 + 1) = 1/2 := by nlinarith [h]
  have h2 : a^2 > 1 := by
    by_contra hc
    push_neg at hc
    have : (a^2 - 1) * (2 * a^4 + 1) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · linarith
      · positivity
    linarith
  have h3 : a^8 = (a^2)^4 := by ring
  rw [h3]
  exact one_lt_pow₀ h2 (by norm_num)
