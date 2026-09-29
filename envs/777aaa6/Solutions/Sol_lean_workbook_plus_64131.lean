-- Prove2me | solution 1 for lean_workbook_plus_64131
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:04.691213+00:00
-- url     : https://prove2.me/submissions/0d0d67c9-f9e6-48d7-9802-d2014b0bdc3f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (f : ℝ → ℝ) (hf: f x = -x * f (1/x)) : f x = -x * f (1/x) := by
  (intros; simp_all)
