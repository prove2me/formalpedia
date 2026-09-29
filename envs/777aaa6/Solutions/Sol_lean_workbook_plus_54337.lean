-- Prove2me | solution 1 for lean_workbook_plus_54337
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:44:40.8335+00:00
-- url     : https://prove2.me/submissions/394a140d-454c-4a10-a02d-faadbf2cb2b8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h : a = b) : |a^2 - b^2| = 0 := by
  (intros; simp_all)
