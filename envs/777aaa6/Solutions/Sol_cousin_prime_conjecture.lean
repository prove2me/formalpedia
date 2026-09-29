-- Prove2me | solution 1 for cousin_prime_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T04:39:49.595308+00:00
-- url     : https://prove2.me/submissions/e26b579d-904d-43ea-8bf5-e8624111d056
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_polignac_conjecture

theorem solution :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 4)}.Infinite := by
  simpa using polignac_conjecture 4 (by decide) (by decide)
