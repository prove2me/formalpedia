-- Prove2me | solution 1 for lean_workbook_plus_13067
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:32:21.026451+00:00
-- url     : https://prove2.me/submissions/105d4784-b66e-42cf-bd63-90182f71e574

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : a > 0) (hb : b > 0) : 1 / (a + b) ≤ 1 / (4 * a) + 1 / (4 * b) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
