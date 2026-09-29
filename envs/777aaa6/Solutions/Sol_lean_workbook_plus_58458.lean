-- Prove2me | solution 1 for lean_workbook_plus_58458
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:08.371668+00:00
-- url     : https://prove2.me/submissions/505245f3-d57a-49f3-8c6a-586ee366d0a3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (2 * a / (a + b) + b / (2 * a)) ≥ 1 / 2 * (3 + (a - b) ^ 2 / (a + b) ^ 2) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
