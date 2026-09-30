-- Prove2me | solution 1 for lean_workbook_plus_18566
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:47:22.378988+00:00
-- url     : https://prove2.me/submissions/182dced2-2f1d-40c5-9b75-662872e32a65

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℝ) (h1 : a+b+c+d=0) (h2 : a*b+b*c+c*d+d*a=0) (h3 : a*b + a*c + a*d + b*c + b*d + c*d=0) (h4 : a^3+b^3+c^3+d^3=0) : a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  have h5 : (a + c) ^ 2 = 0 := by linear_combination (a + c) * h1 - h2
  have h6 : a + c = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h5
  have hc : c = -a := by linarith
  have hd : d = -b := by linarith
  subst hc hd
  have h7 : a ^ 2 + b ^ 2 = 0 := by linear_combination -h3
  have ha2 : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hb2 : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have ha : a = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 ha2
  have hb : b = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hb2
  subst ha hb
  norm_num
