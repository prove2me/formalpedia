-- Prove2me | solution 1 for lean_workbook_plus_63531
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:36.009236+00:00
-- url     : https://prove2.me/submissions/e324f6a2-e279-41b6-bfbc-e1b7e5516b7d

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / a + 1 / b = 1) : a^2 / (a + 2 * b) + b^2 / (b + 2 * a) ≥ 4 / 3   := by
  have hab' := hab
  field_simp [ne_of_gt ha, ne_of_gt hb] at hab'
  have hs : 0 < a + b := add_pos ha hb
  have hs4 : 4 ≤ a + b := by
    by_contra! hn
    have hm : (a + b) * (a + b - 4) < 0 := mul_neg_of_pos_of_neg hs (by linarith)
    nlinarith [sq_nonneg (a - b)]
  have hd : 0 < a + 2 * b := by positivity
  have he : 0 < b + 2 * a := by positivity
  have hbound : (a + b) / 3 ≤ a ^ 2 / (a + 2 * b) + b ^ 2 / (b + 2 * a) := by
    rw [div_add_div _ _ (ne_of_gt hd) (ne_of_gt he)]
    apply (le_div_iff₀ (mul_pos hd he)).2
    nlinarith [mul_nonneg hs.le (sq_nonneg (a - b))]
  linarith

#print axioms solution
