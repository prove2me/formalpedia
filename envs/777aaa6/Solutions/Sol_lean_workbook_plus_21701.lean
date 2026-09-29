-- Prove2me | solution 1 for lean_workbook_plus_21701
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:46.015638+00:00
-- url     : https://prove2.me/submissions/a6d42a86-4a91-4ebc-aa31-23c7d50b142f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n x y z : ℝ) (hn : n > 0) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : n * y * z ≥ 2 * x) : n / 2 ≥ x / (y * z) := by
  (intros; field_simp; nlinarith [sq_nonneg (n), sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (n - x), sq_nonneg (n - y), sq_nonneg (n - z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (n + x), sq_nonneg (n + y), sq_nonneg (n + z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
