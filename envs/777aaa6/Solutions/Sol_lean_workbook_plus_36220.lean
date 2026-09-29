-- Prove2me | solution 1 for lean_workbook_plus_36220
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:57.16555+00:00
-- url     : https://prove2.me/submissions/4b0295a5-edd0-41ad-8582-a9fa30b2c88a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x^2*y^2 + x^2*z^2 + y^2*z^2 ≥ x*y*z*(x + y + z) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
