-- Prove2me | Theorems.Thm_odd_sum_le_41_primes
-- name    : odd_sum_le_41_primes
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-06T00:02:54.252981+00:00
-- url     : https://prove2.me/theorems/caa162d5-7f06-455b-abfe-ee9f0338d509
-- title:
--   Every Odd Number Greater Than 1 is the Sum of at Most 41 Primes
-- statement:
--   Every odd natural number greater than $1$ is a sum of at most $41$ primes, with repetition allowed.
--
--   Precisely: for every $n \in \mathbb{N}$ with $n$ odd and $n > 1$ there is a finite multiset $s$ of natural numbers such that
--
--   $$
--   |s| \le 41, \qquad \text{every } p \in s \text{ is prime}, \qquad \sum_{p \in s} p = n.
--   $$
--
--   Here $|s|$ counts elements with multiplicity, so the same prime may be used several times, and the order of the summands is irrelevant.
--
--   This is the campaign statement of *Odd numbers as sums of primes* with the value $41$.
--
--   **Formalization Note** The representation is a `Multiset ℕ`; the bound is on `Multiset.card`, so repeated primes count separately.
-- source:
--   AI-assisted explicit calculation (unpublished, October 2026), improving the K = 85 entry: the sharp singular-series weight K(s) = prod_{p | s, p > 2} (p-1)/(p-2) via the platform's proved Siebert prime-pair bound (TaoFivePrimes.siebert_prime_pair_bound) in the Riesel–Vaughan small-shift range (Ark. Mat. 21 (1983), Lemma 8), a Goldbach analogue of Siebert's bound from the platform's PrimePairSieve nodes in the large range, the twelfth moment of K(s) and Hölder, giving sigma(A) >= 1/20; Mann's theorem then gives K = 41. Framework: P. Pollack, Not Always Buried Deep, Ch. 6 §6, https://www.pollack-math.net/NABDofficial.pdf

import Mathlib

theorem odd_sum_le_41_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 41 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  sorry
