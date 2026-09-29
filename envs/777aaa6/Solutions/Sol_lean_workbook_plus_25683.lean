-- Prove2me | solution 1 for lean_workbook_plus_25683
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:00.145559+00:00
-- url     : https://prove2.me/submissions/838e3b9a-9d04-4dd5-83ce-fd13008ad21e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => x^2 + x) : ∀ x, f x = x^2 + x := by
  (intros; simp_all)
