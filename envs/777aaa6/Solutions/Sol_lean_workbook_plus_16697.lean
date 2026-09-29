-- Prove2me | solution 1 for lean_workbook_plus_16697
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:46.841936+00:00
-- url     : https://prove2.me/submissions/0738cf93-7a6d-4e98-9d0c-de612f4578d2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (h : ∀ x, f x / x ^ 2 = 0) :
  ∀ x, f x / x = 0 := by
  (intros; simp_all)
