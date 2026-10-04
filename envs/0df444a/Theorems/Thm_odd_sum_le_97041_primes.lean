-- Prove2me | Theorems.Thm_odd_sum_le_97041_primes
-- name    : odd_sum_le_97041_primes
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-03T03:45:45.030685+00:00
-- url     : https://prove2.me/theorems/f2a0e783-2bda-48df-b34e-6219d3d9ca17
-- title:
--   Every Odd Number Greater Than 1 is the Sum of at Most 97041 Primes
-- statement:
--   Every odd natural number greater than $1$ is a sum of at most $97\,041$ primes, with repetition allowed.
--
--   Precisely: for every $n \in \mathbb{N}$ with $n$ odd and $n > 1$ there is a finite multiset $s$ of natural numbers such that
--
--   $$
--   |s| \le 97\,041, \qquad \text{every } p \in s \text{ is prime}, \qquad \sum_{p \in s} p = n.
--   $$
--
--   Here $|s|$ counts elements with multiplicity, so the same prime may be used several times, and the order of the summands is irrelevant.
--
--   This is the campaign statement of *Odd numbers as sums of primes* with the value $97\,041$.
--
--   **Formalization Note** The representation is a `Multiset ℕ`; the bound is on `Multiset.card`, so repeated primes count separately.
-- source:
--   AI-assisted explicit calculation (unpublished, October 2026): the K = 100001 argument with sigma(A) >= 1/35000 and the minimal m = 24260, K = 4m + 1 = 97041; framework: P. Pollack, Not Always Buried Deep, Ch. 6 §6, pp. 196–201, https://www.pollack-math.net/NABDofficial.pdf

import Mathlib

theorem odd_sum_le_97041_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 97041 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  sorry
