-- Prove2me | solution 1 for lean_workbook_plus_14672
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:02.657643+00:00
-- url     : https://prove2.me/submissions/d40ff005-ea5e-4f36-a3d3-d7d90a060e02

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (habc : a * b * c = 1) : a^3 + b^3 + c^3 + d^3 = 1 → a^2 / (1 + b * c * d) + b^2 / (1 + c * d * a) + c^2 / (1 + d * a * b) + d^2 / (1 + a * b * c) ≥ 1 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
