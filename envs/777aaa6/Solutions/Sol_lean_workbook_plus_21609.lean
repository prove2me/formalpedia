-- Prove2me | solution 1 for lean_workbook_plus_21609
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:51.499186+00:00
-- url     : https://prove2.me/submissions/4a3d6630-4f91-45ac-82d4-2441e7225a6a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) : (1 - 1 / a) * (1 - 1 / b) ≥ (1 - 2 / (a + b)) ^ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
