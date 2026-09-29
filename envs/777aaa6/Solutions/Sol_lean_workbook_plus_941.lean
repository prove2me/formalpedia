-- Prove2me | solution 1 for lean_workbook_plus_941
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:12.798608+00:00
-- url     : https://prove2.me/submissions/5c0edfdd-2c8e-4596-aa5f-fecca9dd791c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (hf: f = fun n => 2 - n) : ∀ n, f n = 2 - n := by
  (intros; simp_all)
