-- Prove2me | solution 1 for lean_workbook_plus_58126
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:29.24178+00:00
-- url     : https://prove2.me/submissions/1a9ee73b-f12e-405f-838a-f482625a2173

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b + 1 / 2) ^ 2 ≥ 4 * (a + 1 / 4) * (b + 1 / 4) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
