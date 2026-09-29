-- Prove2me | solution 1 for de_polignac_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T04:43:00.465718+00:00
-- url     : https://prove2.me/submissions/0f1c5cac-61f0-454b-86cc-fcdbce36b110
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_polignac_conjecture

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2 * k)}.Infinite := by
  have hpos : 0 < 2 * k := by omega
  have heven : Even (2 * k) := by
    exact ⟨k, by omega⟩
  simpa using polignac_conjecture (2 * k) hpos heven
