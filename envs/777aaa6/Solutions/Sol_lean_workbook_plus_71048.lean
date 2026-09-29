-- Prove2me | solution 1 for lean_workbook_plus_71048
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:14.087094+00:00
-- url     : https://prove2.me/submissions/75f6d612-b4fd-4664-a63a-cd3d2968a98b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (h : ∀ x, f x = 1) : Set.range f = {1} := by
  (intros; simp_all)
