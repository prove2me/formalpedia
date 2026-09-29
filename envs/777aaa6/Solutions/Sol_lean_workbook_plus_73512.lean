-- Prove2me | solution 1 for lean_workbook_plus_73512
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:50:35.289386+00:00
-- url     : https://prove2.me/submissions/f3086fc3-1279-410a-bcc3-285f1e4c123e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (y^2 + x * z)^2 ≤ (y^2 + x^2) * (y^2 + z^2) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
