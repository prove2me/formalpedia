-- Prove2me | solution 1 for lean_workbook_plus_6168
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:59:07.292939+00:00
-- url     : https://prove2.me/submissions/b8c4d1f2-158c-4c76-bf22-80d2e0a78ec1

import Mathlib
set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 1 / a + 1 / b + 1 / c + 1 / d > 1 / (a + b + c + d)   := by
  have has : a < a+b+c+d := by linarith only [hb, hc, hd]
  have hsmall : 1/(a+b+c+d) < 1/a := one_div_lt_one_div_of_lt ha has
  have hbpos : 0 < 1/b := div_pos (by norm_num) hb
  have hcpos : 0 < 1/c := div_pos (by norm_num) hc
  have hdpos : 0 < 1/d := div_pos (by norm_num) hd
  linarith only [hsmall, hbpos, hcpos, hdpos]

#print axioms solution
