-- Prove2me | solution 1 for lean_workbook_plus_17933
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:58.864677+00:00
-- url     : https://prove2.me/submissions/ee69fa70-1356-4736-b1fe-d6380bc5e937

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : 1 / 2 ≥ a / (b + 2) + b / (a + 2) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb])
