-- Prove2me | solution 1 for lean_workbook_plus_66314
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:32:05.678872+00:00
-- url     : https://prove2.me/submissions/27b6ddc7-8a59-4e00-8837-98aa5c5c9d6a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2 * a ^ 2 + b ^ 2 = 2 * a + b) : 1 - a * b ≥ (a - b) / 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb])
