-- Prove2me | solution 1 for lean_workbook_plus_64463
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:25.566222+00:00
-- url     : https://prove2.me/submissions/a8f30ab8-43ea-4770-a644-6416c2aa04ff

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * (a^2 * b + b^2 * c + c^2 * a) ≤ (a + b + c) * (a^2 + b^2 + c^2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
