-- Prove2me | solution 1 for polignac_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T06:54:54.540573+00:00
-- url     : https://prove2.me/submissions/2a092d29-1ead-496c-9de6-6794f14a2777
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_hardy_littlewood_conjecture_A

theorem solution (k : ℕ) (hk : 0 < k) (hk2 : Even k) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + k)}.Infinite := by
  exact hardy_littlewood_conjecture_A k hk hk2
