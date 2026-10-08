-- Prove2me | Theorems.Thm_odd_sum_le_85_primes
-- name    : odd_sum_le_85_primes
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-05T04:52:30.665784+00:00
-- url     : https://prove2.me/theorems/e60c53f1-41c3-4e5b-9c1d-3b3f6d3fdac9
-- title:
--   Every Odd Number Greater Than 1 is the Sum of at Most 85 Primes
-- statement:
--   Every odd natural number greater than $1$ is a sum of at most $85$ primes, with repetition allowed.
--
--   Precisely: for every $n \in \mathbb{N}$ with $n$ odd and $n > 1$ there is a finite multiset $s$ of natural numbers such that
--
--   $$
--   |s| \le 85, \qquad \text{every } p \in s \text{ is prime}, \qquad \sum_{p \in s} p = n.
--   $$
--
--   Here $|s|$ counts elements with multiplicity, so the same prime may be used several times, and the order of the summands is irrelevant.
--
--   This is the campaign statement of *Odd numbers as sums of primes* with the value $85$.
--
--   **Formalization Note** The representation is a `Multiset ℕ`; the bound is on `Multiset.card`, so repeated primes count separately.
-- source:
--   AI-assisted explicit calculation (unpublished, October 2026), improving the K = 151 entry: Riesel–Vaughan small-shift second moment (Ark. Mat. 21 (1983), Lemma 8) with a fixed-shift prime-pair Selberg sieve, Chebyshev's lower bound psi(x) >= a x - 5 log x + 5 with a = 0.9212 (formalized in PrimeNumberTheoremAnd), and the Hölder large range, giving sigma(A) >= 1/42; Mann's theorem then gives K = 85. Framework: P. Pollack, Not Always Buried Deep, Ch. 6 §6, https://www.pollack-math.net/NABDofficial.pdf

import Mathlib

theorem odd_sum_le_85_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 85 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  sorry
