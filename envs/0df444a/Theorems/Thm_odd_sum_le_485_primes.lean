-- Prove2me | Theorems.Thm_odd_sum_le_485_primes
-- name    : odd_sum_le_485_primes
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-03T22:25:43.19217+00:00
-- url     : https://prove2.me/theorems/9503ab35-eb8f-4296-9574-a4d9be946a50
-- title:
--   Every Odd Number Greater Than 1 is the Sum of at Most 485 Primes
-- statement:
--   Every odd natural number greater than $1$ is a sum of at most $485$ primes, with repetition allowed.
--
--   Precisely: for every $n \in \mathbb{N}$ with $n$ odd and $n > 1$ there is a finite multiset $s$ of natural numbers such that
--
--   $$
--   |s| \le 485, \qquad \text{every } p \in s \text{ is prime}, \qquad \sum_{p \in s} p = n.
--   $$
--
--   Here $|s|$ counts elements with multiplicity, so the same prime may be used several times, and the order of the summands is irrelevant.
--
--   This is the campaign statement of *Odd numbers as sums of primes* with the value $485$.
--
--   **Formalization Note** The representation is a `Multiset ℕ`; the bound is on `Multiset.card`, so repeated primes count separately.
-- source:
--   AI-assisted explicit calculation (unpublished, October 2026), improving the K = 100001 note: weighted eighth-moment / Hölder argument, sigma(A) >= 1/175, m = 121, K = 4m + 1 = 485; framework: P. Pollack, Not Always Buried Deep, Ch. 6 §6, pp. 196–201, https://www.pollack-math.net/NABDofficial.pdf

import Mathlib

theorem odd_sum_le_485_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 485 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  sorry
