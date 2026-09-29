-- Prove2me | solution 1 for lean_workbook_plus_27298
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:45.413433+00:00
-- url     : https://prove2.me/submissions/1603844d-4745-46ca-bc2d-28cdc2fade65

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f g : ℝ → ℝ) (b : ℝ) (hf : ∀ x, f (b + x) = f (b - x)) (hg : ∀ x, g (f (b + x)) = g (f (b - x))) : ∀ x, g (f (b + x)) = g (f (b - x)) := by
  (intros; simp_all)
