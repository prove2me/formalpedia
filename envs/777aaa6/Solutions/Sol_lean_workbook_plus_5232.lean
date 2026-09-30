-- Prove2me | solution 1 for lean_workbook_plus_5232
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:43:44.769216+00:00
-- url     : https://prove2.me/submissions/7dabf7ee-68f5-41ad-a883-ddda2ad99c24

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) : |x - y| ≤ |2 * x + y| + |x + 2 * y| := by
  have h : x - y = (2 * x + y) - (x + 2 * y) := by ring
  rw [h]
  exact abs_sub _ _
