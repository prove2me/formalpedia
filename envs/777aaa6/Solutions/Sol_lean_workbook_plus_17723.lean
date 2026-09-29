-- Prove2me | solution 1 for lean_workbook_plus_17723
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:57.152721+00:00
-- url     : https://prove2.me/submissions/a5fdad6e-b40d-4d3f-88ca-10b5ebd81958

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hxy : x ≥ y) (hy : y ≥ 0) : (x / (1 + y)) ≥ (y / (y + 1)) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
