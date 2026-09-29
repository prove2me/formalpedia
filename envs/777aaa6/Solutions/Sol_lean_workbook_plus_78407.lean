-- Prove2me | solution 1 for lean_workbook_plus_78407
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:26.404559+00:00
-- url     : https://prove2.me/submissions/05a6bfb9-72f1-470b-8ca5-8848c30bda89

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 0) (h2 : a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c = 1) : 2 * a * b * c ≤ 1 := by
  (intros; linarith)
