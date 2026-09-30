-- Prove2me | solution 2 for lean_workbook_plus_60138
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:11.079871+00:00
-- url     : https://prove2.me/submissions/668afc80-a93e-44ab-82f8-836a56f84d76

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : a ≤ b) (hc : b ≤ c) : (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
