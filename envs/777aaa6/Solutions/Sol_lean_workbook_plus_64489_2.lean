-- Prove2me | solution 2 for lean_workbook_plus_64489
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:33.326592+00:00
-- url     : https://prove2.me/submissions/b7873428-733a-45b1-a180-dda2f91fbc15

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab: a^2+b^2 >= c^2+d^2) : b / (a + c) + a / (b + d) ≥ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
