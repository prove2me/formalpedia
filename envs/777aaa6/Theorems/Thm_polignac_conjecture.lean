-- Prove2me | Theorems.Thm_polignac_conjecture
-- name    : polignac_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:29:25.00458+00:00
-- url     : https://prove2.me/theorems/230ff68f-c554-419a-a695-e7098f6cd176
-- statement:
--   **Polignac's Conjecture**: For every even positive integer $k$, there are infinitely many prime pairs $(p, p+k)$.
--
--   The twin prime conjecture is the special case $k=2$. Cousin primes ($k=4$): $(3,7),(7,11),(13,17),...$; sexy primes ($k=6$): $(5,11),(7,13),(11,17),...$
--
--   Proposed by Alphonse de Polignac in 1849. Yitang Zhang's 2013 breakthrough implies there exists some even $k \leq 246$ for which this holds, but the specific values remain unproven.
-- source:
--   https://en.wikipedia.org/wiki/Polignac%27s_conjecture

import Mathlib

theorem polignac_conjecture (k : ℕ) (hk : 0 < k) (hk2 : Even k) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + k)}.Infinite := by
  sorry
