-- Prove2me | solution 1 for lean_workbook_plus_9577
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:18.056622+00:00
-- url     : https://prove2.me/submissions/afe1340a-ddd0-403a-9582-ff97e00976a1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (x^2 + 3 * x * y + y^2)^2 * (2 * x^2 + 3 * x * y + 2 * y^2) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
