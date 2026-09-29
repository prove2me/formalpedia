-- Prove2me | solution 1 for lean_workbook_plus_49641
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:21.904704+00:00
-- url     : https://prove2.me/submissions/8e81b7e0-917f-4bde-a07d-bc617742fd55

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) : (x * z) ^ 2 + (y * x) ^ 2 + (z * y) ^ 2 ≥ x * y * z * (x + y + z) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
