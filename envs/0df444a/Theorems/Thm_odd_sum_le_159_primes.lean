-- Prove2me | Theorems.Thm_odd_sum_le_159_primes
-- name    : odd_sum_le_159_primes
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-04T23:58:33.963161+00:00
-- url     : https://prove2.me/theorems/999529f0-7a11-475d-8593-bca2bd240895
-- title:
--   Every Odd Number Greater Than 1 is the Sum of at Most 159 Primes
-- statement:
--   Every odd natural number greater than $1$ is a sum of at most $159$ primes, with repetition allowed.
--
--   Precisely: for every $n \in \mathbb{N}$ with $n$ odd and $n > 1$ there is a finite multiset $s$ of natural numbers such that
--
--   $$
--   |s| \le 159, \qquad \text{every } p \in s \text{ is prime}, \qquad \sum_{p \in s} p = n.
--   $$
--
--   Here $|s|$ counts elements with multiplicity, so the same prime may be used several times, and the order of the summands is irrelevant.
--
--   This is the campaign statement of *Odd numbers as sums of primes* with the value $159$.
--
--   **Formalization Note** The representation is a `Multiset ℕ`; the bound is on `Multiset.card`, so repeated primes count separately.
-- source:
--   AI-assisted explicit calculation (unpublished, October 2026), improving the K = 241 entry: Riesel–Vaughan small-shift second moment (Ark. Mat. 21 (1983), Lemma 8) with a fixed-shift prime-pair Selberg sieve, Mathlib's Chebyshev bound psi(x) >= x log 2 - O(log x), and the Hölder large range, giving sigma(A) >= 1/79; Mann's theorem then gives K = 159. Framework: P. Pollack, Not Always Buried Deep, Ch. 6 §6, https://www.pollack-math.net/NABDofficial.pdf

import Mathlib

theorem odd_sum_le_159_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 159 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  sorry
