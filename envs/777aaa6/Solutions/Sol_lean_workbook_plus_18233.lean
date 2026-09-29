-- Prove2me | solution 1 for lean_workbook_plus_18233
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:23.723662+00:00
-- url     : https://prove2.me/submissions/a1d4665d-06fd-46b4-a08a-e09f5408b23b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) (h : x = a / b) (h' : y = b / c) (h'' : z = c / a) : a * b * c ≥ (a + b - c) * (a + c - b) * (b + c - a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (x), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - x), sq_nonneg (b - c), sq_nonneg (b - x), sq_nonneg (c - x), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + x), sq_nonneg (b + c), sq_nonneg (b + x), sq_nonneg (c + x), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
