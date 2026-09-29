-- Prove2me | solution 1 for lean_workbook_plus_4250
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:28.780192+00:00
-- url     : https://prove2.me/submissions/1af2bdcd-d6db-4cc6-9e93-6edf6e1124fe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (h : f (-1) = -1) : f (-1) = -1 := by
  (intros; simp_all)
