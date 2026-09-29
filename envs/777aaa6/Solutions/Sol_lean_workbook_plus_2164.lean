-- Prove2me | solution 1 for lean_workbook_plus_2164
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:15:55.568083+00:00
-- url     : https://prove2.me/submissions/54123d01-cffd-4921-90a9-5bf51278a76e

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ∃ n : ℕ, p ∣ 2 ^ n - 1 := by
  refine ⟨p-1, ?_⟩
  apply Nat.dvd_of_mod_eq_zero
  exact Nat.pow_card_sub_one_sub_one_mod_card hp (Nat.coprime_two_left.2 (hp.odd_of_ne_two hp2))
