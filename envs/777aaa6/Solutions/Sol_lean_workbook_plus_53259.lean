-- Prove2me | solution 1 for lean_workbook_plus_53259
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:21:45.981007+00:00
-- url     : https://prove2.me/submissions/14d03739-d188-421c-85bc-b0c5fec7b156

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^2 ≥ 4 * b) : 5 * (a^2 * b^2 - a * b) + 8 ≥ 9 * b^2 * (b + 1) := by
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sub_nonneg.2 hab), sq_nonneg (a*b - 1), sq_nonneg (b - 1), sq_nonneg (a - 2), mul_nonneg hb (sub_nonneg.2 hab), sq_nonneg (a - 2*b), mul_nonneg (mul_nonneg hb hb) (sub_nonneg.2 hab)]
