-- Prove2me | Theorems.Thm_edenic_semiprime_not_prime
-- name    : edenic_semiprime_not_prime
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T07:28:06.28504+00:00
-- url     : https://prove2.me/theorems/57371981-ebce-45dd-90f3-5ff94a9bd872
-- title:
--   Edenic semiprimes are never prime
-- statement:
--   No Edenic semiprime $n = p(p+2)$ is itself prime.
--
--   Both factors exceed $1$: $p \neq 1$ since $p$ is prime, and $p + 2 \geq 4$. A product of two integers greater than $1$ is never prime, so $n$ is composite.
--
--   **Formalization.** `Nat.not_prime_mul` applied to the two non-unit side conditions; $p \ge 2$ is `Nat.Prime.two_le` and closes $p + 2 \neq 1$ by `omega`.
--
--   **Reuse.** Together with `edenic_semiprime_ge_15` this shows every Edenic semiprime is a *proper* composite sitting above the first prime pair — the family contains no primes at all.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_not_prime (n : ℕ) (h : IsEdenicSemiprime n) : ¬n.Prime := by
  sorry
