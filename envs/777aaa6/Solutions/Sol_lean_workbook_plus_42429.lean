-- Prove2me | solution 1 for lean_workbook_plus_42429
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:34.383466+00:00
-- url     : https://prove2.me/submissions/ee9f45d3-8102-4d4a-9c6b-64423cd8da1d

import Mathlib
set_option autoImplicit false

theorem solution  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 0) :
  f⁻¹' Set.Icc (-1) 1 = Set.univ ∧ f '' Set.univ = {0}   := by
  simp [Set.ext_iff, h₀]

#print axioms solution
