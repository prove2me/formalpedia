-- Prove2me | solution 1 for lean_workbook_plus_13497
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:41.344595+00:00
-- url     : https://prove2.me/submissions/5ae885aa-b042-4e15-8534-e0cc34a6d390

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (bd : ℤ) (h₁ : bd = -5) : bd = -5 := by
  (intros; simp_all)
