-- Prove2me | solution 1 for lean_workbook_plus_4260
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:00.200504+00:00
-- url     : https://prove2.me/submissions/c584b323-10d0-4d02-ac68-334abda6b038

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : 1 / a^2 + 1 / b^2 + 1 / c^2 ≥ 3 + 2 * (a^3 + b^3 + c^3) / (a * b * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
