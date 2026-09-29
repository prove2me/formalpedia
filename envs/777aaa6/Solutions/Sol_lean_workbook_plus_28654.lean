-- Prove2me | solution 1 for lean_workbook_plus_28654
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:41:18.426769+00:00
-- url     : https://prove2.me/submissions/1b7531f7-8fb5-47aa-a71b-3af2b8c9d27d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * a ^ 2 * b ^ 2 + 2 * a ^ 2 * c ^ 2 + 2 * b ^ 2 * c ^ 2 ≥ 2 * a * b + 2 * a * c + 2 * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
