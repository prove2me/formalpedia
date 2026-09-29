-- Prove2me | solution 1 for lean_workbook_plus_45538
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:39.484289+00:00
-- url     : https://prove2.me/submissions/58c77349-a3d3-4a8d-8d71-9c1054ae7e9c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0) : 4 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 3 * (x * y + y * z + x * z) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
