-- Prove2me | solution 1 for lean_workbook_plus_11053
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:47:43.521229+00:00
-- url     : https://prove2.me/submissions/786b3d3e-9f9b-48b0-8cb1-58a46793542a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (x ^ 2 + x * y + y ^ 2) * (4 / 3) ≥ (x + y) ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
