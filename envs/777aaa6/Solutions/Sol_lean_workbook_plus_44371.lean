-- Prove2me | solution 1 for lean_workbook_plus_44371
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:00.274679+00:00
-- url     : https://prove2.me/submissions/060d021e-5ed0-4215-978c-e01fd46cacff

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : x^3 + y^3 + z^3 - 3 * x * y * z ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
