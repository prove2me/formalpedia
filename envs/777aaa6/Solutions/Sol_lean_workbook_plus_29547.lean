-- Prove2me | solution 1 for lean_workbook_plus_29547
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:09:27.048083+00:00
-- url     : https://prove2.me/submissions/f20218ae-cdc2-496b-b10c-8440a230c9a9

import Mathlib.Analysis.Complex.Basic

theorem solution {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^3 + b^3 = a - b) : (a - b)^4 ≤ (1 - 4 * a * b) * (1 - a * b)^2 := by
  have hd : 0 ≤ a - b := by rw [← hab]; positivity
  rcases hd.lt_or_eq with hlt | heq
  · -- a > b : homogenize with 1 · (a - b) = a^3 + b^3
    have hA : (1 - 4 * a * b) * (a - b) = a^3 + b^3 - 4 * a^2 * b + 4 * a * b^2 := by
      linear_combination (-1 : ℝ) * hab
    have hB : (1 - a * b) * (a - b) = a^3 + b^3 - a^2 * b + a * b^2 := by
      linear_combination (-1 : ℝ) * hab
    have hD : (a - b)^7 = (a - b)^6 * (a^3 + b^3) := by rw [hab]; ring
    have key : ((1 - 4 * a * b) * (1 - a * b)^2 - (a - b)^4) * (a - b)^3
        = 4 * a * b^6 * (3 * b^2 - 3 * a * b + 2 * a^2) := by
      calc ((1 - 4 * a * b) * (1 - a * b)^2 - (a - b)^4) * (a - b)^3
          = ((1 - 4 * a * b) * (a - b)) * ((1 - a * b) * (a - b))^2 - (a - b)^7 := by ring
        _ = (a^3 + b^3 - 4 * a^2 * b + 4 * a * b^2) * (a^3 + b^3 - a^2 * b + a * b^2)^2
              - (a - b)^6 * (a^3 + b^3) := by rw [hA, hB, hD]
        _ = 4 * a * b^6 * (3 * b^2 - 3 * a * b + 2 * a^2) := by ring
    have hq : 0 ≤ 3 * b^2 - 3 * a * b + 2 * a^2 := by
      nlinarith [sq_nonneg (4 * a - 3 * b), sq_nonneg b]
    have hpos : 0 ≤ ((1 - 4 * a * b) * (1 - a * b)^2 - (a - b)^4) * (a - b)^3 := by
      rw [key]; positivity
    have h3 : 0 < (a - b)^3 := by positivity
    have := nonneg_of_mul_nonneg_left hpos h3
    linarith
  · -- a = b forces a = b = 0
    have hab' : a = b := by linarith
    subst hab'
    have h3 : a^3 = 0 := by linarith
    have h0 : a = 0 := pow_eq_zero_iff (by norm_num) |>.mp h3
    subst h0
    norm_num
