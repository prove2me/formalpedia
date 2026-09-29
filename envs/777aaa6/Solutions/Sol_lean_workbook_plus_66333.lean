-- Prove2me | solution 1 for lean_workbook_plus_66333
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:32:10.575522+00:00
-- url     : https://prove2.me/submissions/4fdf6208-2ff7-4293-b300-e08c99d1e96a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (f_def : ∀ x, f x = x^(1/2)) : f 2 = 2^(1/2) := by
  (intros; simp_all)
