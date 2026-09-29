-- Prove2me | solution 1 for lean_workbook_plus_23693
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:46:51.759285+00:00
-- url     : https://prove2.me/submissions/13e143b2-de84-4329-9cab-368c7d6bac12

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (g : ℝ → ℝ) (hg : ∀ x ≥ 0, g x ≤ g 0) : ∀ x ≥ 0, g x ≤ g 0 := by
  (intros; simp_all)
