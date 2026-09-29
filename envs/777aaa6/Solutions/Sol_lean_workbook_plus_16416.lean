-- Prove2me | solution 1 for lean_workbook_plus_16416
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:13.569019+00:00
-- url     : https://prove2.me/submissions/81759645-12ed-4eb7-939c-24985ce92583

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hpq: p + q + r = 1) : p^2 + q^2 + r^2 ≥ 1 / 3 := by
  (intros; nlinarith [sq_nonneg (p), sq_nonneg (q), sq_nonneg (r), sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (q - r), sq_nonneg (p + q), sq_nonneg (p + r), sq_nonneg (q + r), mul_pos hp hq, mul_pos hp hr, mul_pos hq hr])
