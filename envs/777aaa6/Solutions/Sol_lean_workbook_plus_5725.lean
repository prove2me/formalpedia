-- Prove2me | solution 1 for lean_workbook_plus_5725
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:07:08.786363+00:00
-- url     : https://prove2.me/submissions/7e269154-1cb5-49ad-846e-e7d3d58d2a8f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y z : ℝ) (hy : y > 0) (hz : z > 0) : (y + z) / (4 * y * z) ≥ 1 / (y + z) := by
  (intros; field_simp; nlinarith [sq_nonneg (y), sq_nonneg (z), sq_nonneg (y - z), sq_nonneg (y + z)])
