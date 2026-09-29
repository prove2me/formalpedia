-- Prove2me | solution 1 for lean_workbook_plus_19172
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:00.818196+00:00
-- url     : https://prove2.me/submissions/792ca2a5-cda6-44ed-9da0-298607f64129

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (e : ℝ) (h₁ : e < 0) : (-e / 2004) > 0 := by
  (intros; simp_all)
