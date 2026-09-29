-- Prove2me | solution 1 for lean_workbook_plus_16739
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:33.352712+00:00
-- url     : https://prove2.me/submissions/7db2fb53-83b0-43c2-8824-810915ce181a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hpq : p + q + r = 1) (hpqr : p * q * r = 1) (h : r ≥ p * (4 * q - p ^ 2) / 9) : q ≤ p ^ 3 + 36 / (4 * p + 9) := by
  (intros; nlinarith [sq_nonneg (p), sq_nonneg (q), sq_nonneg (r), sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (q - r), sq_nonneg (p + q), sq_nonneg (p + r), sq_nonneg (q + r), mul_pos hp hq, mul_pos hp hr, mul_pos hq hr])
