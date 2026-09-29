-- Prove2me | solution 1 for lean_workbook_plus_32954
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:06:08.548964+00:00
-- url     : https://prove2.me/submissions/3cab97bd-7d4b-4d75-90c5-8d716c014108

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => 1 - x) : ∀ x, f x = 1 - x := by
  (intros; simp_all)
