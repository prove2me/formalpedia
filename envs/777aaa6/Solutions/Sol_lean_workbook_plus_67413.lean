-- Prove2me | solution 1 for lean_workbook_plus_67413
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:02.747702+00:00
-- url     : https://prove2.me/submissions/53dd21da-4d26-4596-8382-73c82a459be1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (x : ℝ) (h : f = fun (x : ℝ) => x - 1) : f x = x - 1 := by
  (intros; simp_all)
