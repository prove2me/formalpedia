-- Prove2me | solution 2 for strong_goldbach_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T14:47:33.652388+00:00
-- url     : https://prove2.me/submissions/edb94b32-8d03-450f-b51d-515cf21b60ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_goldbach

theorem solution : ∀ n : ℕ, 4 ≤ n → 2 ∣ n →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  intro n hn hdvd
  exact goldbach n (by omega) (even_iff_two_dvd.mpr hdvd)
