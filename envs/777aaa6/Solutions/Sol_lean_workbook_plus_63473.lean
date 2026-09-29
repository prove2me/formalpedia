-- Prove2me | solution 1 for lean_workbook_plus_63473
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:08:16.254184+00:00
-- url     : https://prove2.me/submissions/53f9c027-9e18-44b2-b8f5-35a6411994cc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a + b > c) (hb : a + c > b) (hc : b + c > a) : 1 / 4 * (b ^ 2 + c ^ 2) ≥ 1 / 2 * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
