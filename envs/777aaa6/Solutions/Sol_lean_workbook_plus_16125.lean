-- Prove2me | solution 1 for lean_workbook_plus_16125
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:20:57.793546+00:00
-- url     : https://prove2.me/submissions/fb9e5a1b-0303-40ed-a30a-e5c9e6dd8357

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: ∀ x > 0, f x = x) : ∀ x > 0, f x = x := by
  (intros; simp_all)
