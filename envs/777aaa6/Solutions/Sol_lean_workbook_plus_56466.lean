-- Prove2me | solution 1 for lean_workbook_plus_56466
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:11.147328+00:00
-- url     : https://prove2.me/submissions/adbdc1a2-de0f-4ac2-9ac9-a6748148eb55

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x ↦ -x^2 / 2) : ∀ x, f x = -x^2 / 2 := by
  (intros; simp_all)
