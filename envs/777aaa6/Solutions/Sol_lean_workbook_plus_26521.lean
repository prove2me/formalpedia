-- Prove2me | solution 1 for lean_workbook_plus_26521
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:25:42.50879+00:00
-- url     : https://prove2.me/submissions/743e759a-f653-4c1a-ac0e-7c8ac9853323

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f 0 = 1) : f 0 = 1 := by
  (intros; simp_all)
