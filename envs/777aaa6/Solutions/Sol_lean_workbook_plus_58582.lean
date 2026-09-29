-- Prove2me | solution 1 for lean_workbook_plus_58582
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:52.724588+00:00
-- url     : https://prove2.me/submissions/99231da0-3461-4459-a24c-75008efa269a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) :  x * x + y * y + z * z ≥ x * y + y * z + z * x := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
