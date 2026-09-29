-- Prove2me | solution 1 for lean_workbook_plus_63835
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:53.057075+00:00
-- url     : https://prove2.me/submissions/6d8747c6-f384-4cd7-b4b0-0cb31d808d41

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (t : ℝ) (ht1 : t ≥ 1) : (t - 1) ^ 2 * (7 * t ^ 2 - 4 * t + 1) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (t)])
