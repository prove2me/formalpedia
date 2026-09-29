-- Prove2me | solution 1 for lean_workbook_plus_59355
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:43:46.173909+00:00
-- url     : https://prove2.me/submissions/56eb5ccf-c414-471e-8d16-264c50ce64ff

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : x ≤ 320 ∧ y ≥ 2200 ↔ x ≤ 320 ∧ y ≥ 2200 := by
  norm_num
