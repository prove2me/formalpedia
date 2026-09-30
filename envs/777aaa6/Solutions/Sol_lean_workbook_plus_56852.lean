-- Prove2me | solution 1 for lean_workbook_plus_56852
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:36.74878+00:00
-- url     : https://prove2.me/submissions/ca8b862d-8355-451e-b97b-f17e22ab6493

import Mathlib
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f ∘ f = id) : Function.Bijective f   := by
  rw [Function.bijective_iff_has_inverse]
  use f
  simp only [Function.leftInverse_iff_comp, Function.rightInverse_iff_comp]
  exact ⟨hf, hf⟩

#print axioms solution
