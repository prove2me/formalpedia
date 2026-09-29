-- Prove2me | solution 1 for lean_workbook_plus_25769
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:42:30.417821+00:00
-- url     : https://prove2.me/submissions/09d7c3ed-7eeb-480b-a776-2469560f489b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (h : ∀ x, f x = 3 * x - 4) : f 2016 = 6044 := by
  (intros; simp_all)
