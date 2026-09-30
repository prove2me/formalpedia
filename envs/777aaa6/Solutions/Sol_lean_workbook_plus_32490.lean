-- Prove2me | solution 1 for lean_workbook_plus_32490
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:22:46.208825+00:00
-- url     : https://prove2.me/submissions/044960db-3d72-4604-8794-d6e106242bc9

import Mathlib

set_option autoImplicit false

theorem polynomial_residue (x : Int) : (x^4+x+1) % 2 = 1 := by
  have hc : x ≡ 0 [ZMOD 2] ∨ x ≡ 1 [ZMOD 2] := by
    simp only [Int.ModEq]
    omega
  rcases hc with h | h
  · simpa [Int.ModEq] using ((h.pow 4).add h).add (Int.ModEq.refl 1)
  · simpa [Int.ModEq] using ((h.pow 4).add h).add (Int.ModEq.refl 1)

theorem solution : ¬ (∃ x : Int, x^4+x+1 ≡ 0 [ZMOD 2]) := by
  rintro ⟨x, hx⟩
  have hzero : (x^4+x+1) % 2 = 0 := by simpa [Int.ModEq] using hx
  rw [polynomial_residue] at hzero
  contradiction

#print axioms solution
