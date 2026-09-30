-- Prove2me | solution 1 for lean_workbook_plus_6876
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:21:48.546391+00:00
-- url     : https://prove2.me/submissions/17d8d5d9-a48f-4f5c-9c03-fa7a56cc171c

import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false

theorem solution : ∀ {a b : ℕ}, b ∣ a → (2 ^ b - 1) ∣ (2 ^ a - 1) := by
  intro a b h
  exact Nat.pow_sub_one_dvd_pow_sub_one 2 h

#print axioms solution
