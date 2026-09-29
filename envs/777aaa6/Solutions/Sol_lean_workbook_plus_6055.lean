-- Prove2me | solution 1 for lean_workbook_plus_6055
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:57.66339+00:00
-- url     : https://prove2.me/submissions/12ded00e-57fb-4af2-a2cb-97069c21545d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (f : ℝ → ℝ → ℝ) (hf: ∀ u v : ℝ, u * v < 0 → f u v = a) : ∀ u v : ℝ, u * v < 0 → f u v = a := by
  (intros; simp_all)
