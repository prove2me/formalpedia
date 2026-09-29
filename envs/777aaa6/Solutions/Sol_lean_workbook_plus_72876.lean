-- Prove2me | solution 1 for lean_workbook_plus_72876
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:21:21.713039+00:00
-- url     : https://prove2.me/submissions/c9d48cbf-7a3c-4458-91c6-44976e7921c5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : 1/3 * x * y * z ≥ Real.sqrt 3) : x * y * z ≥ 3 * Real.sqrt 3 := by
  (intros; linarith)
