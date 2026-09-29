-- Prove2me | solution 1 for lean_workbook_plus_3100
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:07.086826+00:00
-- url     : https://prove2.me/submissions/11c021eb-4ed9-4749-aaa7-94e9657b8867

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun (x:ℝ) => x) : ∀ x > 0, f x = x := by
  (intros; simp_all)
