-- Prove2me | Theorems.Thm_edenic_semiprime_odd
-- name    : edenic_semiprime_odd
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T06:11:02.645436+00:00
-- url     : https://prove2.me/theorems/49051407-3b75-43ea-a3a5-0d0f490221a5
-- title:
--   Edenic semiprimes are odd
-- statement:
--   An **Edenic semiprime** $n = p(p+2)$, a product of two primes differing by $2$, is odd.
--
--   If $p = 2$ then $p + 2 = 4$ is not prime, so $p$ is an odd prime and so is $p+2$; a product of two odd numbers is odd. Equivalently, no Edenic semiprime is even, and the whole family sits inside the odd numbers — the first qualitative consequence of the pair being twinned.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_odd (n : ℕ) (h : IsEdenicSemiprime n) : Odd n := by
  sorry
