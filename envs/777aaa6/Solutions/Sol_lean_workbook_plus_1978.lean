-- Prove2me | solution 1 for lean_workbook_plus_1978
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:25.253882+00:00
-- url     : https://prove2.me/submissions/ab6a1410-2518-4222-a83d-e5b03e7e59b5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a ^ 4 + a ^ 4 + b ^ 4 + c ^ 4 ≥ 4 * a ^ 2 * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
