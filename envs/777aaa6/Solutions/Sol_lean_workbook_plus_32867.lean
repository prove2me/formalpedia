-- Prove2me | solution 1 for lean_workbook_plus_32867
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:40.968908+00:00
-- url     : https://prove2.me/submissions/0070c3d5-4b39-437b-8d18-a40cf01a1b30

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a / b + b / a ≥ (a + 1) / (b + 1) + (b + 1) / (a + 1) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
