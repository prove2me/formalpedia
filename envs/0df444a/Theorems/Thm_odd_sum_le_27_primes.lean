-- Prove2me | Theorems.Thm_odd_sum_le_27_primes
-- name    : odd_sum_le_27_primes
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-06T17:35:29.353953+00:00
-- url     : https://prove2.me/theorems/c7a1b70a-16d7-43a2-bc52-30bca8c7b2af
-- title:
--   Every Odd Number Greater Than 1 is the Sum of at Most 27 Primes
-- statement:
--   Every odd natural number greater than $1$ is a sum of at most $27$ primes, with repetition allowed.
--
--   Precisely: for every $n \in \mathbb{N}$ with $n$ odd and $n > 1$ there is a finite multiset $s$ of natural numbers such that
--
--   $$
--   |s| \le 27, \qquad \text{every } p \in s \text{ is prime}, \qquad \sum_{p \in s} p = n.
--   $$
--
--   Here $|s|$ counts elements with multiplicity, so the same prime may be used several times, and the order of the summands is irrelevant.
--
--   This is the campaign statement of *Odd numbers as sums of primes* with the value $27$.
--
--   **Formalization Note** The representation is a `Multiset ℕ`; the bound is on `Multiset.card`, so repeated primes count separately.
-- source:
--   AI-assisted explicit calculation (unpublished, October 2026), improving the K = 41 entry: Riesel-Vaughan's singular-series-weighted large range (Ark. Mat. 21 (1983), Sec. 8) with Dirichlet characters and the platform's weighted large sieve (MVSieve nodes), the Riesel-Vaughan small-shift range (Lemma 8) with Siebert's prime-pair bound (TaoFivePrimes.siebert_prime_pair_bound), and Chebyshev's psi(x) >= 0.9212x - 5 log x + 5 in place of Rosser-Schoenfeld, giving sigma(A) >= 1/13; Mann's theorem then gives K = 27. Framework: P. Pollack, Not Always Buried Deep, Ch. 6 Sec. 6, https://www.pollack-math.net/NABDofficial.pdf

import Mathlib

theorem odd_sum_le_27_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 27 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  sorry
