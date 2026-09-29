-- Prove2me | solution 1 for lean_workbook_plus_3573
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:17:08.973972+00:00
-- url     : https://prove2.me/submissions/183b2671-bd94-4889-869d-3110e24703ba

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a r : ℝ)
  (n : ℕ)
  (h₀ : a = -1)
  (h₁ : r = 1)
  (h₂ : n = 0)
  (h₃ : ∑' n : ℕ, (a * r^n + 1) = 0) :
  ∑' n : ℕ, (a * r^n + 1) = 0 := by
  (intros; simp_all)
