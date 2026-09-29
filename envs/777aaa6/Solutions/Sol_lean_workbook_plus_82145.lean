-- Prove2me | solution 1 for lean_workbook_plus_82145
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:35:52.655648+00:00
-- url     : https://prove2.me/submissions/79414eda-752c-4f93-b4d3-6f4f8d7af485

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y p : ℝ) (r : ℝ) : x + p ∈ Metric.ball (x + y) r ↔ p ∈ Metric.ball y r := by
  norm_num
