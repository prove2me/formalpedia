-- Prove2me | solution 1 for lean_workbook_plus_49540
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:11.796365+00:00
-- url     : https://prove2.me/submissions/79cf9636-f10a-47a0-be89-ecced875ff14

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 8 * (a^4 + b^4) ≥ (a + b)^4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
