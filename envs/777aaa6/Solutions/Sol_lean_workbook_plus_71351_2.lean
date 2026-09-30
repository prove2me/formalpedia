-- Prove2me | solution 2 for lean_workbook_plus_71351
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:38.999515+00:00
-- url     : https://prove2.me/submissions/bd85f258-216c-4d89-90dd-6e25f7804061

import Mathlib.Analysis.Complex.Basic

theorem solution {a b u v : ℝ} (ha : a > 0) (hb : b > 0) (hv : v > 0) (hab : a + b = 2 * u) (h : a * b = v ^ 2) : a ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2 - 2) ≥ (a + b) * (a * b - 1) := by
  -- a + b ≥ 2 v, since (a+b)^2 ≥ 4ab = 4v^2 and a + b + 2v > 0
  have hs' : a + b - 2 * v ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 * v), sq_nonneg (a + b + 2 * v)]
  -- the bracket v^4 (a+b+2v) - (v^2 - 1) is nonnegative
  have h1 : v ^ 4 * (a + b + 2 * v) - (v ^ 2 - 1) ≥ 0 := by
    have h4 : v ^ 4 * (a + b - 2 * v) ≥ 0 := mul_nonneg (by positivity) hs'
    have h5 : 4 * v ^ 5 - v ^ 2 + 1 ≥ 0 := by
      rcases le_or_gt v 1 with hv1 | hv1
      · nlinarith [pow_pos hv 5, mul_nonneg hv.le hv.le]
      · have hv3 : v ^ 3 ≥ 1 := by nlinarith [mul_pos hv hv]
        have hv5 : v ^ 5 ≥ v ^ 2 := by nlinarith [mul_nonneg (pow_pos hv 2).le (sub_nonneg.mpr hv3)]
        nlinarith [pow_pos hv 2]
    nlinarith
  -- 2 v (v^2 - 1)(v^3 - 1) ≥ 0
  have h2 : 2 * v * (v ^ 2 - 1) * (v ^ 3 - 1) ≥ 0 := by
    have e : 2 * v * (v ^ 2 - 1) * (v ^ 3 - 1) = 2 * v * (v - 1) ^ 2 * ((v + 1) * (v ^ 2 + v + 1)) := by ring
    rw [e]
    apply mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
    apply mul_nonneg (by linarith)
    nlinarith [sq_nonneg (v + 1 / 2)]
  -- key identity
  have e1 : a ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2 - 2) - (a + b) * (a * b - 1)
      = (a + b - 2 * v) * (v ^ 4 * (a + b + 2 * v) - (v ^ 2 - 1)) + 2 * v * (v ^ 2 - 1) * (v ^ 3 - 1) := by
    linear_combination ((a * b + v ^ 2) * (a + b) ^ 2 - 2 * ((a * b) ^ 2 + a * b * v ^ 2 + v ^ 4) - 2 * (a * b + v ^ 2) - (a + b)) * h
  have := mul_nonneg hs' h1
  linarith
