-- Prove2me | solution 1 for lean_workbook_plus_34323
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:43.688469+00:00
-- url     : https://prove2.me/submissions/04c10a26-c7fb-4b45-ae04-b4fe537fea68

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ)
  (h₀ : ∀ x, f (x + 1) = f x) :
  ∀ a, f (a + 1) = f a := by
  (intros; simp_all)
