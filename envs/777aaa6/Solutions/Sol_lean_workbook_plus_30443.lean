-- Prove2me | solution 1 for lean_workbook_plus_30443
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:33.395473+00:00
-- url     : https://prove2.me/submissions/fd99f7fd-39ec-451c-946b-007348a840a6

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : 0 ≤ x) : (x^2 + 1)^6 / 2^7 + 1 / 2 ≥ x^5 - x^3 + x := by
  have hq : 0 ≤ x^10 + 2*x^9 + 9*x^8 + 16*x^7 + 38*x^6 + 60*x^5 + 102*x^4 + 16*x^3 - 55*x^2 + 2*x + 65 := by
    nlinarith [sq_nonneg (x^2 - 55/204), pow_nonneg hx 10, pow_nonneg hx 9, pow_nonneg hx 8,
      pow_nonneg hx 7, pow_nonneg hx 6, pow_nonneg hx 5, pow_nonneg hx 3]
  have key : (x^2 + 1)^6 / 2^7 + 1 / 2 - (x^5 - x^3 + x)
      = (x - 1)^2 * (x^10 + 2*x^9 + 9*x^8 + 16*x^7 + 38*x^6 + 60*x^5 + 102*x^4 + 16*x^3 - 55*x^2 + 2*x + 65) / 128 := by
    ring
  have : 0 ≤ (x - 1)^2 * (x^10 + 2*x^9 + 9*x^8 + 16*x^7 + 38*x^6 + 60*x^5 + 102*x^4 + 16*x^3 - 55*x^2 + 2*x + 65) / 128 := by
    positivity
  linarith
