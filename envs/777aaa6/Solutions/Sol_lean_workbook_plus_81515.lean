-- Prove2me | solution 1 for lean_workbook_plus_81515
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:37:53.975637+00:00
-- url     : https://prove2.me/submissions/fa0620d2-30ff-4da9-824b-95e12af520a8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (2 / (x + y + 2) - 1 / ((x + 1) * (y + 2))) ≤ 1 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_nonneg hx hy])
