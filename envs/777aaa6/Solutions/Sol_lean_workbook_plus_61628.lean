-- Prove2me | solution 1 for lean_workbook_plus_61628
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:20:11.102294+00:00
-- url     : https://prove2.me/submissions/a6a56140-f22b-4cab-b0e1-503cb5e8278d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (f : ℝ → ℝ) (hf: f x = 1 / (x + 1)) : f x = 1 / (x + 1) := by
  (intros; simp_all)
