-- Prove2me | solution 1 for lean_workbook_plus_54565
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:16.246526+00:00
-- url     : https://prove2.me/submissions/7e402004-4d1e-4fa1-b46b-f628ff6b259b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f g : ℝ → ℝ) (hg : Function.Injective g) (hgf : Function.Injective (g ∘ f)) : Function.Injective f := by
  (intros; simp_all)
