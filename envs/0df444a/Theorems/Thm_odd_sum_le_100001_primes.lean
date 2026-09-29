-- Prove2me | Theorems.Thm_odd_sum_le_100001_primes
-- name    : odd_sum_le_100001_primes
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:34:15.950978+00:00
-- url     : https://prove2.me/theorems/15dad269-473d-4159-b6ed-d76a66964527
-- title:
--   Every Odd Number Greater Than 1 is the Sum of at Most 100001 Primes
-- statement:
--   Every odd natural number greater than $1$ is a sum of at most $100\,001$ primes, with repetition allowed.
--
--   Precisely: for every $n \in \mathbb{N}$ with $n$ odd and $n > 1$ there is a finite multiset $s$ of natural numbers such that
--
--   $$
--   |s| \le 100\,001, \qquad \text{every } p \in s \text{ is prime}, \qquad \sum_{p \in s} p = n.
--   $$
--
--   Here $|s|$ counts elements with multiplicity, so the same prime may be used several times, and the order of the summands is irrelevant.
--
--   This is the campaign statement of *Odd numbers as sums of primes* with the value $100\,001$. The constant comes from Schnirelmann's elementary sieve-and-density method with all constants made explicit, which avoids the prime number theorem.
--
--   **Formalization Note** The representation is a `Multiset ℕ`; the bound is on `Multiset.card`, so repeated primes count separately.
-- source:
--   An explicit elementary constant for sums of primes (unpublished note, September 2026), Theorem 1 (constant K = 4m + 1 = 100001, Section 6); framework: P. Pollack, Not Always Buried Deep, Ch. 6 §6, pp. 196–201, https://www.pollack-math.net/NABDofficial.pdf

import Mathlib

theorem odd_sum_le_100001_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 100001 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  sorry
