-- Prove2me | solution 1 for lean_workbook_plus_908
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:05.846925+00:00
-- url     : https://prove2.me/submissions/bffb126f-b99a-452a-99e8-a56d47d0264c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℤ) (h : x ≥ y + 1) : x ≥ y + 1 := by
  (intros; simp_all)
