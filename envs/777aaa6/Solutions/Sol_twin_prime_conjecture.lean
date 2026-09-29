-- Prove2me | solution 1 for twin_prime_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T04:32:08.65173+00:00
-- url     : https://prove2.me/submissions/cad9f91b-0e3d-4d08-96b5-b24a6bccd98f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_polignac_conjecture

theorem solution :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by
  simpa using polignac_conjecture 2 (by decide) (by decide)
