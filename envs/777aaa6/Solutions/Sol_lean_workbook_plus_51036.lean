-- Prove2me | solution 1 for lean_workbook_plus_51036
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:30.065595+00:00
-- url     : https://prove2.me/submissions/c31d49c5-05c3-4bf6-b21c-055355e09be9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y: ℝ) (h : abs x ≥ abs y) : (abs x / (abs x + 2008)) ≥ (abs y / (abs y + 2008)) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
