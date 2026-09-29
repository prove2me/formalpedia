-- Prove2me | solution 1 for lean_workbook_plus_20585
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:39.303073+00:00
-- url     : https://prove2.me/submissions/9acd93bb-54a4-4022-89c2-2bb5060fb4a8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (f : ℝ → ℝ) (hf: f x = f 0) : f x = f 0 := by
  (intros; simp_all)
