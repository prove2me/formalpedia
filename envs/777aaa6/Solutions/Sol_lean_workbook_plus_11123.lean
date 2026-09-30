-- Prove2me | solution 1 for lean_workbook_plus_11123
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:51:03.011127+00:00
-- url     : https://prove2.me/submissions/2432aec6-9ca5-477d-99e4-6ebf5ace79ce

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x y : ℤ, (x^2 ≡ -y [ZMOD 4]) → (y ≡ 0 [ZMOD 4]) ∨ (y ≡ -1 [ZMOD 4])   := by
  intro x y h
  have hx : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  have hp : x ^ 2 ≡ (x % 4) ^ 2 [ZMOD 4] := (Int.mod_modEq x 4).symm.pow 2
  have hy : -y ≡ (x % 4) ^ 2 [ZMOD 4] := h.symm.trans hp
  rcases hx with hx | hx | hx | hx <;> norm_num [Int.ModEq, hx] at hy ⊢ <;> omega

#print axioms solution
