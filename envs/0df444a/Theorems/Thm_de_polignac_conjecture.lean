-- Prove2me | Theorems.Thm_de_polignac_conjecture
-- name    : de_polignac_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:28:18.757461+00:00
-- url     : https://prove2.me/theorems/d77cdf8b-722c-4fba-9ab3-7d6b673dfef4
-- statement:
--   De Polignac's conjecture (1849): For every even number 2k, there are infinitely many pairs of consecutive primes differing by 2k. The k=1 case is the twin prime conjecture. Zhang (2013) proved some bounded gap; Maynard-Tao (2013) improved to gap ≤ 246. No specific gap is proved to occur infinitely often.
-- source:
--   https://en.wikipedia.org/wiki/Polignac%27s_conjecture

import Mathlib

import Mathlib

theorem de_polignac_conjecture (k : ℕ) (hk : 1 ≤ k) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2 * k)}.Infinite := by
  sorry
