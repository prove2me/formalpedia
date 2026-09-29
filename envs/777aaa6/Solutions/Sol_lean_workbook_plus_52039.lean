-- Prove2me | solution 1 for lean_workbook_plus_52039
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:18.788937+00:00
-- url     : https://prove2.me/submissions/77724010-195d-48fa-ab30-21650cf493a7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 2 * x + 1 / 3)
  (h₁ : x = 0) :
  f x = 1 / 3 := by
  (intros; simp_all)
