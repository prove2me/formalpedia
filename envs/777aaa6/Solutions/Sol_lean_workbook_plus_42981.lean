-- Prove2me | solution 1 for lean_workbook_plus_42981
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:24.249135+00:00
-- url     : https://prove2.me/submissions/cdfdc634-0a18-4812-a25a-7ae2da37d638

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x > 2) (h₂ : y > 2) (h₃ : x < y) :
  x + (4 / (4 + x)) < y + (4 / (4 + y)) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
