-- Prove2me | solution 1 for lean_workbook_plus_73232
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:50:40.827118+00:00
-- url     : https://prove2.me/submissions/bd096b19-8f6a-4a26-924a-c4ce3a440330

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : x = 3 / 2) (h₂ : y = 3 / 2) (h₃ : z = 4 / 9) (h₄ : x * y * z = 1) : x = 3 / 2 ∧ y = 3 / 2 ∧ z = 4 / 9 := by
  (intros; simp_all)
