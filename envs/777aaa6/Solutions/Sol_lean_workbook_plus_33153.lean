-- Prove2me | solution 1 for lean_workbook_plus_33153
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:21:16.791839+00:00
-- url     : https://prove2.me/submissions/97e76865-cab3-48ce-82fe-b64d25a55f4f

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a + b) * (b + c) * (c + a) = 8) : (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) ≤ 8 * (2 - a * b * c)^6 := by
  -- (a+b)(b+c)(c+a) - 8abc = a(b-c)² + b(c-a)² + c(a-b)²
  have key : a * (b - c)^2 + b * (c - a)^2 + c * (a - b)^2 = 0 := by
    linear_combination h - 8 * habc
  have t1 := mul_nonneg ha.le (sq_nonneg (b - c))
  have t2 := mul_nonneg hb.le (sq_nonneg (c - a))
  have t3 := mul_nonneg hc.le (sq_nonneg (a - b))
  have h1 : a * (b - c)^2 = 0 := by linarith
  have h2 : b * (c - a)^2 = 0 := by linarith
  have hbc : b = c := by
    rcases mul_eq_zero.mp h1 with h | h
    · linarith
    · have := (pow_eq_zero_iff two_ne_zero).mp h; linarith
  have hca : c = a := by
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · have := (pow_eq_zero_iff two_ne_zero).mp h; linarith
  subst hbc
  subst hca
  have e : (b^2 + b * b) * (b^2 + b * b) * (b^2 + b * b) = 8 * (b * b * b)^2 := by ring
  rw [e, habc]
  norm_num
