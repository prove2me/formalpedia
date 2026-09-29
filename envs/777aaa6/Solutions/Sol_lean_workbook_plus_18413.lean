-- Prove2me | solution 1 for lean_workbook_plus_18413
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:42.051577+00:00
-- url     : https://prove2.me/submissions/33589773-2c3b-43a4-a6bf-08c38f2b90df

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (x : ℝ) (hf: f x = if x >= 0 then x^2 else 1) : f x = if x >= 0 then x^2 else 1 := by
  (intros; simp_all)
