-- Prove2me | solution 1 for lean_workbook_plus_45467
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:38:23.245957+00:00
-- url     : https://prove2.me/submissions/41812fd6-9af3-4605-821c-26593aa28b52

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a + 2 * a * b * c = 1) : 1 / (a + b + 2) + 1 / (b + c + 2) + 1 / (c + a + 2) ≤ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
