-- Prove2me | solution 1 for lean_workbook_plus_41239
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:25.052081+00:00
-- url     : https://prove2.me/submissions/ee71d6ac-5407-4a59-992f-db8367508b3d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y: ℝ) : (x + y) ^ 2 ≥ 4 * x * y := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
