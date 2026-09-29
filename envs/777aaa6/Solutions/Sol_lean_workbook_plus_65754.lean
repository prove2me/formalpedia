-- Prove2me | solution 1 for lean_workbook_plus_65754
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:05:37.353255+00:00
-- url     : https://prove2.me/submissions/34e14a76-b879-455e-8d9a-131b29c55e0b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : ¬ x > y) : x ≤ y := by
  (intros; simp_all)
