-- Prove2me | solution 1 for lean_workbook_plus_17785
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:43:27.749605+00:00
-- url     : https://prove2.me/submissions/4e0810de-0c5a-48e3-87f2-80b2ac6e9763

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℤ) (h : a = -7 ∨ a = 5) : a = -7 ∨ a = 5 := by
  (intros; simp_all)
