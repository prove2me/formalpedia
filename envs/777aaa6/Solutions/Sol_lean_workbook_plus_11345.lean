-- Prove2me | solution 1 for lean_workbook_plus_11345
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:05.366199+00:00
-- url     : https://prove2.me/submissions/22a0136c-280f-4daa-8366-71b8a4fce4c8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => x + 1) : ∀ x, f x = x + 1 := by
  (intros; simp_all)
