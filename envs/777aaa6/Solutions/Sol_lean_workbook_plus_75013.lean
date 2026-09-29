-- Prove2me | solution 1 for lean_workbook_plus_75013
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:57.851582+00:00
-- url     : https://prove2.me/submissions/decca2bd-6c0c-4eb6-9e72-8781bc6d8b67

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x₁ h₁ : ℝ) (p : ℝ) (hp : p = 2 * Real.sqrt 2) : h₁ = x₁ + p ↔ h₁ = x₁ + 2 * Real.sqrt 2 := by
  (intros; simp_all)
