-- Prove2me | Theorems.Thm_edenic_semiprime_succ_not_prime
-- name    : edenic_semiprime_succ_not_prime
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T07:27:59.262344+00:00
-- url     : https://prove2.me/theorems/e250b691-3f37-4052-83f9-325ba39e987e
-- title:
--   No successor of an Edenic semiprime is prime
-- statement:
--   For every Edenic semiprime $n$, the number $n + 1$ is composite.
--
--   Since $n = p(p+2)$ with $p \ge 2$,
--   $$n + 1 = p(p+2) + 1 = (p+1)^2,$$
--   a perfect square with base $p + 1 \ge 3 > 1$; a square $(p+1)(p+1)$ of an integer $> 1$ is not prime.
--
--   **Formalization.** Expand the square by `ring`, rewrite, then `Nat.not_prime_mul` with both side conditions discharged by `omega` from $p \ge 2$.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_succ_not_prime (n : ℕ) (h : IsEdenicSemiprime n) :
    ¬(n + 1).Prime := by
  sorry
