-- Prove2me | solution 1 for lean_workbook_plus_33772
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:31.25304+00:00
-- url     : https://prove2.me/submissions/44db6fb1-1327-42f5-8b77-eca926719c85

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (f : ℝ → ℝ) (hf: f x = 1) : f x = 1 := by
  (intros; simp_all)
