-- Prove2me | solution 1 for lean_workbook_plus_42372
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:46.346192+00:00
-- url     : https://prove2.me/submissions/887e1d64-949a-46d7-bd06-0244881e042e

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : 2 = x^2 + y^2 + z^2) (h₂ : x^2 + y^2 ≥ 2 * x * y) : 1 - x * y ≥ 0 ∧ 1 - x * z ≥ 0 ∧ 1 - y * z ≥ 0   := by
  refine ⟨?_, ?_, ?_⟩
  · nlinarith only [h₁, h₂, sq_nonneg z]
  · nlinarith only [h₁, sq_nonneg (x - z), sq_nonneg y]
  · nlinarith only [h₁, sq_nonneg (y - z), sq_nonneg x]

#print axioms solution
