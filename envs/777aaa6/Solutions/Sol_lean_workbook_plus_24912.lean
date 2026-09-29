-- Prove2me | solution 1 for lean_workbook_plus_24912
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:37.694725+00:00
-- url     : https://prove2.me/submissions/0f7212bb-98ee-4d15-846b-93e95bed6e26

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : 0 < a ∧ 0 < b) : 4 * (a^3 + b^3) ≥ (a + b)^3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
