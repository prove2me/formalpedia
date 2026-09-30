-- Prove2me | solution 1 for lean_workbook_plus_64376
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:35.505552+00:00
-- url     : https://prove2.me/submissions/c1dfcc0f-3b61-420b-ba8b-08af890cb8f4

import Mathlib
set_option autoImplicit false

theorem solution {a b : ℝ} (h1 : a > b) (h2 : b > 0) (h3 : a^5 + b^5 = a - b) : a^4 + b^4 < 1   := by
  have ha : 0 < a := lt_trans h2 h1
  have hb5 : 0 < b ^ 5 := pow_pos h2 5
  have ha4 : a ^ 4 < 1 := by
    by_contra hn
    have hp := mul_nonneg ha.le (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith [h3]
  have hb3 : b ^ 3 < a ^ 3 := by
    have hp : 0 < (a - b) * (a ^ 2 + a * b + b ^ 2) :=
      mul_pos (by linarith) (by positivity)
    nlinarith
  have hab3 : a * b ^ 3 < 1 := calc
    a * b ^ 3 < a * a ^ 3 := mul_lt_mul_of_pos_left hb3 ha
    _ = a ^ 4 := by ring
    _ < 1 := ha4
  have hp : 0 < b * (1 + b ^ 4 - a * b ^ 3) :=
    mul_pos h2 (by nlinarith [pow_nonneg h2.le 4])
  by_contra hn
  have hq : a * (1 - a ^ 4 - b ^ 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha.le (by linarith)
  nlinarith [h3]

#print axioms solution
