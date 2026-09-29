-- Prove2me | solution 1 for lean_workbook_plus_29372
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:28.368077+00:00
-- url     : https://prove2.me/submissions/de1c0217-af6c-4f4d-99ea-aa5d317a3824

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ)
  (h₁ : ∃ x : ℚ, a = x)
  (h₂ : ∃ x : ℚ, b = x)
  (h₃ : ∃ x : ℚ, a + b = x)
  (h₄ : ∃ x : ℚ, a - b = x)
  (h₅ : ∃ x : ℚ, a * b = x) :
  ∃ x : ℚ, a = x ∧ ∃ x : ℚ, b = x := by
  (intros; simp_all)
