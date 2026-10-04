-- Prove2me | Theorems.Thm_odd_sum_le_6101_primes
-- name    : odd_sum_le_6101_primes
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-03T03:51:38.542216+00:00
-- url     : https://prove2.me/theorems/e849e49a-9430-47e2-b36a-ff22bf0d67a4
-- title:
--   Every Odd Number Greater Than 1 is the Sum of at Most 6101 Primes
-- statement:
--   Every odd natural number greater than $1$ is a sum of at most $6101$ primes, with repetition allowed.
--
--   Precisely: for every $n \in \mathbb{N}$ with $n$ odd and $n > 1$ there is a finite multiset $s$ of natural numbers such that
--
--   $$
--   |s| \le 6101, \qquad \text{every } p \in s \text{ is prime}, \qquad \sum_{p \in s} p = n.
--   $$
--
--   Here $|s|$ counts elements with multiplicity, so the same prime may be used several times, and the order of the summands is irrelevant.
--
--   This is the campaign statement of *Odd numbers as sums of primes* with the value $6101$.
--
--   **Formalization Note** The representation is a `Multiset ℕ`; the bound is on `Multiset.card`, so repeated primes count separately.
-- source:
--   AI-assisted explicit calculation (unpublished, October 2026): weighted second-moment / Cauchy–Schwarz argument, sigma(A) >= 1/2200, m = 1525, K = 4m + 1 = 6101; framework: P. Pollack, Not Always Buried Deep, Ch. 6 §6, pp. 196–201, https://www.pollack-math.net/NABDofficial.pdf

import Mathlib

theorem odd_sum_le_6101_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 6101 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  sorry
