-- Prove2me | solution 1 for lean_workbook_plus_19119
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:23:03.503997+00:00
-- url     : https://prove2.me/submissions/d02ebbbd-ff6a-4f07-9254-ac89b1f66955

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a ^ 3 + b ^ 3 + c ^ 3 + a * b * c = 4) : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 3 * a * b * c ≥ 6 := by
  -- From a^3+b^3+c^3 = 3 = 3abc we get a = b = c, then a^3 = 1 so a = 1.
  have hsum : a ^ 3 + b ^ 3 + c ^ 3 = 3 := by linarith
  have hprod : (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) = 0 := by
    nlinarith [hsum, habc]
  have hpos : 0 < a + b + c := by linarith
  have hsq : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hprod with h1 | h1
    · linarith
    · exact h1
  have hab : a = b := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hbc : b = c := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  subst hab
  subst hbc
  have h3 : a ^ 3 = 1 := by nlinarith
  have ha1 : a = 1 := (pow_eq_one_iff_of_nonneg ha.le (by norm_num : (3:ℕ) ≠ 0)).mp h3
  rw [ha1]
  have e : (1:ℝ) / 1 ^ 2 = 1 := by rw [one_pow, div_one]
  rw [e]
  linarith
