-- Prove2me | solution 1 for lean_workbook_plus_9855
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:28.149167+00:00
-- url     : https://prove2.me/submissions/ee76aef2-1512-4fe9-a933-ba968f2f8a45

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (2 * a / (a + b) + b / (2 * a)) ≥ 1 / 2 * ((a - b) / (a + b)) ^ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
