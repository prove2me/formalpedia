-- Prove2me | solution 1 for lean_workbook_plus_10522
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:40.548687+00:00
-- url     : https://prove2.me/submissions/c494d26c-5156-462c-9702-6a35f23b5f11

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (x : ℝ) (h₁ : f x = x) : f (f x) = x := by
  (intros; simp_all)
