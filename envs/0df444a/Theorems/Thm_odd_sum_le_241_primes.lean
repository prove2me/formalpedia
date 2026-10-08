-- Prove2me | Theorems.Thm_odd_sum_le_241_primes
-- name    : odd_sum_le_241_primes
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-04T19:52:10.140631+00:00
-- url     : https://prove2.me/theorems/96ed5cc8-d457-44e4-b024-0de09fac4316
-- title:
--   Every Odd Number Greater Than 1 is the Sum of at Most 241 Primes
-- statement:
--   Every odd natural number greater than $1$ is a sum of at most $241$ primes, with repetition allowed.
--
--   Precisely: for every $n \in \mathbb{N}$ with $n$ odd and $n > 1$ there is a finite multiset $s$ of natural numbers such that
--
--   $$
--   |s| \le 241, \qquad \text{every } p \in s \text{ is prime}, \qquad \sum_{p \in s} p = n.
--   $$
--
--   Here $|s|$ counts elements with multiplicity, so the same prime may be used several times, and the order of the summands is irrelevant.
--
--   This is the campaign statement of *Odd numbers as sums of primes* with the value $241$.
--
--   **Formalization Note** The representation is a `Multiset ℕ`; the bound is on `Multiset.card`, so repeated primes count separately.
-- source:
--   AI-assisted explicit calculation (unpublished, October 2026), improving the K = 100001 note: sigma(A) >= 1/120 via a weighted sixteenth-moment / Hölder argument, then Mann's theorem gives 240B = N, K = 241; framework: P. Pollack, Not Always Buried Deep, Ch. 6 §6 (incl. Mann's theorem), https://www.pollack-math.net/NABDofficial.pdf

import Mathlib

theorem odd_sum_le_241_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 241 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  sorry
