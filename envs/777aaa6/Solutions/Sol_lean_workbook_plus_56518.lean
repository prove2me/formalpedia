-- Prove2me | solution 1 for lean_workbook_plus_56518
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:17.286191+00:00
-- url     : https://prove2.me/submissions/fea0fea9-cc5c-456a-84ba-6406a83dd247

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (a b : ℝ) (hf: f = fun x ↦ a * x ^ 2 + b * x) : ∀ x, f x = a * x ^ 2 + b * x := by
  (intros; simp_all)
