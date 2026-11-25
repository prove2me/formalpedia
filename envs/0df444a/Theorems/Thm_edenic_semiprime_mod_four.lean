-- Prove2me | Theorems.Thm_edenic_semiprime_mod_four
-- name    : edenic_semiprime_mod_four
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T06:11:03.955794+00:00
-- url     : https://prove2.me/theorems/bffbe3cd-2e27-4388-bff0-4b34b706984a
-- title:
--   Edenic semiprimes are 3 modulo 4
-- statement:
--   Every Edenic semiprime satisfies
--   $$n \equiv 3 \pmod 4.$$
--
--   Write the odd prime as $p = 2k+1$. Then
--   $$n = (2k+1)(2k+3) = 4k^2 + 8k + 3 \equiv 3 \pmod 4.$$
--
--   Thus Edenic semiprimes land in the residue class $3 \bmod 4$ — the class that is never a square and never a sum of two squares, which is what makes the non-square and non-sum-of-two-squares properties below automatic.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_mod_four (n : ℕ) (h : IsEdenicSemiprime n) : n % 4 = 3 := by
  sorry
