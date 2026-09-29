-- Prove2me | solution 1 for lean_workbook_plus_31159
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:07.571352+00:00
-- url     : https://prove2.me/submissions/e9506dd8-7dbe-4c39-8e10-89fca6704b3b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (h : ∀ x, f (x + 1) = f x + 1) : ∀ x, f (x + 1) = f x + 1 := by
  (intros; simp_all)
