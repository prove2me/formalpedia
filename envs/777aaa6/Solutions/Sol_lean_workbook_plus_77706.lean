-- Prove2me | solution 1 for lean_workbook_plus_77706
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:50:08.264895+00:00
-- url     : https://prove2.me/submissions/18070e5d-dbce-41c3-8c63-e51e10b45203

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (x + 2 * y + z) * (y + 2 * z + x) * (z + 2 * x + y) ≥ (3 * x + z) * (3 * y + x) * (3 * z + y) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
