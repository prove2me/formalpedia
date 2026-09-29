-- Prove2me | solution 1 for lean_workbook_plus_38314
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:13.200118+00:00
-- url     : https://prove2.me/submissions/53f8f3ea-1f7c-48b2-8412-ce7e0a061fa6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (1 / (3 * a + 1) + 1 / (3 * b + 1)) ≥ 4 / (3 * (a + b) + 2) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
