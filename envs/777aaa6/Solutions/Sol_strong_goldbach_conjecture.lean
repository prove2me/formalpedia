-- Prove2me | solution 1 for strong_goldbach_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T06:33:49.950718+00:00
-- url     : https://prove2.me/submissions/d4279776-116b-43f4-9fea-9fb2d562dbf9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_goldbach

theorem solution :
    ∀ n : ℕ, 4 ≤ n → 2 ∣ n →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  intro n hn hdiv
  apply goldbach n (by omega)
  exact (even_iff_two_dvd).2 hdiv
