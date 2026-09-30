-- Prove2me | solution 1 for lean_workbook_plus_71320
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:27.033837+00:00
-- url     : https://prove2.me/submissions/7b174152-4b13-4745-96f4-a0af62659727

import Mathlib
set_option autoImplicit false

theorem solution : ∀ (x : ℤ), (x ^ 2 ≡ 0 [ZMOD 4]) ∨ (x ^ 2 ≡ 1 [ZMOD 4]) := by
  intro x
  have hr : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  have hs := (Int.mod_modEq x 4).symm.pow 2
  change x ^ 2 % 4 = (x % 4) ^ 2 % 4 at hs
  change x ^ 2 % 4 = 0 % 4 ∨ x ^ 2 % 4 = 1 % 4
  rcases hr with hr | hr | hr | hr <;> norm_num [hr] at hs ⊢ <;> omega

#print axioms solution
