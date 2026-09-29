-- Prove2me | solution 1 for lean_workbook_plus_71136
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:22.456585+00:00
-- url     : https://prove2.me/submissions/0b8771f5-5d54-4940-b934-1ab10ff53a3d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : -1 < x ∧ x < 0) (hy : 0 < y ∧ y < 1) :
  x^2 + x*y + y^2 < 1 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
