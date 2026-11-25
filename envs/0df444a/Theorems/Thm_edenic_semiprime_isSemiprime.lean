-- Prove2me | Theorems.Thm_edenic_semiprime_isSemiprime
-- name    : edenic_semiprime_isSemiprime
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T06:11:19.888798+00:00
-- url     : https://prove2.me/theorems/649d9dc3-7551-43ba-b93b-b8e349375749
-- title:
--   Edenic semiprimes are semiprimes
-- statement:
--   Every Edenic semiprime is a semiprime in the sense of `Nat.IsSemiprime`: it has exactly two prime factors counted with multiplicity,
--   $$\Omega(n) = 2.$$
--
--   Indeed $n = p(p+2)$ with $p$ and $p+2$ prime, so $\Omega(n) = \Omega(p) + \Omega(p+2) = 1 + 1 = 2$ by `Nat.Prime.mul_isAlmostPrime_two`. Hence the Edenic family is a subfamily of the $P_2$ class studied in sieve theory and in Chen's theorem.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_isSemiprime (n : ℕ) (h : IsEdenicSemiprime n) :
    Nat.IsSemiprime n := by
  sorry
