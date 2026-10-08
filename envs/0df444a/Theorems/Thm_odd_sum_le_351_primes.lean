-- Prove2me | Theorems.Thm_odd_sum_le_351_primes
-- name    : odd_sum_le_351_primes
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-03T22:25:51.471986+00:00
-- url     : https://prove2.me/theorems/fd5b2548-746a-4183-ac89-977fa8baf419
-- title:
--   Every Odd Number Greater Than 1 is the Sum of at Most 351 Primes
-- statement:
--   Every odd natural number greater than $1$ is a sum of at most $351$ primes, with repetition allowed.
--
--   Precisely: for every $n \in \mathbb{N}$ with $n$ odd and $n > 1$ there is a finite multiset $s$ of natural numbers such that
--
--   $$
--   |s| \le 351, \qquad \text{every } p \in s \text{ is prime}, \qquad \sum_{p \in s} p = n.
--   $$
--
--   Here $|s|$ counts elements with multiplicity, so the same prime may be used several times, and the order of the summands is irrelevant.
--
--   This is the campaign statement of *Odd numbers as sums of primes* with the value $351$.
--
--   **Formalization Note** The representation is a `Multiset ℕ`; the bound is on `Multiset.card`, so repeated primes count separately.
-- source:
--   AI-assisted explicit calculation (unpublished, October 2026), improving the K = 100001 note: sigma(A) >= 1/175 via a weighted eighth-moment / Hölder argument, then Mann's theorem gives 350B = N, K = 351; framework: P. Pollack, Not Always Buried Deep, Ch. 6 §6 (incl. Mann's theorem), https://www.pollack-math.net/NABDofficial.pdf

import Mathlib

theorem odd_sum_le_351_primes (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 351 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  sorry
