-- Prove2me | Theorems.Thm_edenic_semiprime_factors_unique
-- name    : edenic_semiprime_factors_unique
-- status  : Open
-- author  : @mwm
-- created : 2026-11-25T07:28:11.700805+00:00
-- url     : https://prove2.me/theorems/ee9d1ae8-037c-4129-a524-9299dae9228d
-- title:
--   Factorization of an Edenic semiprime into two primes is unique up to order
-- statement:
--   If $n = p(p+2)$ is Edenic and $n = q r$ with $q, r$ prime, then $\{q, r\} = \{p, p+2\}$: the twin pair is recovered uniquely up to order.
--
--   Since $q \mid p(p+2)$ and $q$ is prime, $q \mid p$ or $q \mid (p+2)$; primality then forces $q = p$ or $q = p + 2$ (the case $q = 1$ is excluded). In the first case cancelling $p$ from $p(p+2) = pr$ gives $r = p+2$; in the second, cancelling $p+2$ gives $r = p$.
--
--   **Formalization.** `Nat.Prime.dvd_mul` splits the divisibility, `Nat.dvd_prime` extracts the equality, and `Nat.mul_left_cancel` (using $p > 0$) performs the cancellation.
--
--   **Reuse.** Uniqueness makes the witness $p$ of `IsEdenicSemiprime` canonical — downstream results may speak of *the* twin pair of $n$ without choice.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_factors_unique (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ p, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2) ∧
      ∀ q r : ℕ, q.Prime → r.Prime → n = q * r → (q = p ∧ r = p + 2) ∨ (q = p + 2 ∧ r = p) := by
  sorry
