-- Prove2me | solution 1 for lean_workbook_plus_69179
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:56:04.387635+00:00
-- url     : https://prove2.me/submissions/7da06f43-6e4a-433f-a8ef-fdcfb9d3db86

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false

theorem solution (a : ℝ) : √(a ^ 2) = |a| := by
  exact Real.sqrt_sq_eq_abs a
