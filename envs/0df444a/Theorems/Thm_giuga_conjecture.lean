-- Prove2me | Theorems.Thm_giuga_conjecture
-- name    : giuga_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:54:56.167954+00:00
-- url     : https://prove2.me/theorems/5ca0e444-eeb9-4686-b6ef-fb9ebb2e3a3b
-- statement:
--   **Giuga's Conjecture**: $n$ is prime if and only if $\sum_{k=1}^{n-1} k^{n-1} \equiv -1 \pmod{n}$.
--
--   Proposed by Giuseppe Giuga (1950). The forward direction (prime $\Rightarrow$ congruence) follows from Fermat's little theorem. The backward direction is open. Any counterexample would be a Giuga number that is not prime, and must have at least 14,000 digits. Related to Agoh's conjecture and Bernoulli numbers.
--
--   **Source**: Giuga, G. (1950). Su una presumibile proprietà caratteristica dei numeri primi. Ist. Lombardo Sci. Lett. Rend. A., 83, 511–528.
-- source:
--   https://en.wikipedia.org/wiki/Giuga_number

import Mathlib

theorem giuga_conjecture (n : ℕ) (hn : 2 ≤ n) :
    Nat.Prime n ↔
      (∑ k ∈ Finset.Icc 1 (n - 1), (k : ZMod n) ^ (n - 1)) = (-1 : ZMod n) := by
  sorry
