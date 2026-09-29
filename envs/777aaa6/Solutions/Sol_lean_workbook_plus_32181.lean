-- Prove2me | solution 1 for lean_workbook_plus_32181
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:31.726299+00:00
-- url     : https://prove2.me/submissions/d6fd75c4-8517-41fd-90cb-e54834a53651

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : Real.sqrt x * Real.sqrt y = Real.sqrt (x * y) := by
  (intros; simp_all)
