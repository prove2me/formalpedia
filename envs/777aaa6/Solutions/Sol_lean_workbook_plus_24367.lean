-- Prove2me | solution 1 for lean_workbook_plus_24367
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:26.041526+00:00
-- url     : https://prove2.me/submissions/c04c5f28-3659-44b4-abc1-e2cbc8f0b175

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => x / 5) : ∀ x ∈ Set.Ico (0:ℝ) 10, f x = x / 5 := by
  (intros; simp_all)
