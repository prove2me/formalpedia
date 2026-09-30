-- Prove2me | solution 1 for lean_workbook_plus_64522
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:15:43.852144+00:00
-- url     : https://prove2.me/submissions/543be3c8-358a-47a1-91ce-5ee2276955ed

import Mathlib
set_option autoImplicit false

theorem solution (p : ℕ) (hp : p.Prime) (x : ZMod p) (hx : x ≠ 0) : ∃ y, x * y = 1   := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨x⁻¹, mul_inv_cancel₀ hx⟩

#print axioms solution
