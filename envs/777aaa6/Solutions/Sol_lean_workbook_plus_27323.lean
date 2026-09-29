-- Prove2me | solution 1 for lean_workbook_plus_27323
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:43.055681+00:00
-- url     : https://prove2.me/submissions/61fc91f0-32fb-4470-9393-e4bb0e1342ac

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (x : ℝ) (hf: f x = 1/x) (hx : 0 < x) : f x = 1/x := by
  (intros; simp_all)
