-- Prove2me | solution 1 for lean_workbook_plus_54866
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:49.472861+00:00
-- url     : https://prove2.me/submissions/01af9a71-3576-41ea-8466-ae58ea053958

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x + y) * (y + z) * (z + x) * (x + y + z) ≥ x * (y + z) ^ 3 + y * (z + x) ^ 3 + z * (x + y) ^ 3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
