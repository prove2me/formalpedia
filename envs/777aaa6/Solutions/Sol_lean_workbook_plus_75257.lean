-- Prove2me | solution 1 for lean_workbook_plus_75257
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:53:06.932282+00:00
-- url     : https://prove2.me/submissions/921e7415-eada-4fdf-bc76-448c9ff69464

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: ∀ x ≥ 0, f x = x) : ∀ x ≥ 0, f x = x := by
  (intros; simp_all)
