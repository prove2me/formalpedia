-- Prove2me | solution 1 for lean_workbook_plus_1810
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:44.740479+00:00
-- url     : https://prove2.me/submissions/93fcf4ee-5ed7-4bb9-b1d7-bac61ce46913

import Mathlib

theorem solution (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) :
    1 / (2 * a ^ 3 + 1) * (a ^ 3 + 2) +
      1 / (2 * b ^ 3 + 1) * (b ^ 3 + 2) +
      1 / (2 * c ^ 3 + 1) * (c ^ 3 + 2) ≥ 1 / 3 := by
  have h (x : ℝ) (hx : 0 < x) : 1 / 2 ≤ 1 / (2 * x ^ 3 + 1) * (x ^ 3 + 2) := by
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
    nlinarith
  linarith [h a ha.1, h b ha.2.1, h c ha.2.2.1]
