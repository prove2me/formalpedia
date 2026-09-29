-- Prove2me | solution 1 for lean_workbook_plus_78004
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:24:28.331864+00:00
-- url     : https://prove2.me/submissions/0effd2d8-884e-4f5c-bac9-f024facbeca8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℝ) (hb : b > 0) (hc : c > 0) : (b^2 / c + c) ≥ 2 * b := by
  (intros; field_simp; nlinarith [sq_nonneg (b), sq_nonneg (c), sq_nonneg (b - c), sq_nonneg (b + c)])
