-- Prove2me | Theorems.Thm_edenic_semiprime_succ_is_square
-- name    : edenic_semiprime_succ_is_square
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T06:10:52.794845+00:00
-- url     : https://prove2.me/theorems/39f2f30d-7cd7-5b2d-b415-4cd98b9f7712
-- title:
--   An Edenic semiprime plus one is a perfect square
-- statement:
--   If $n = p(p+2)$ is Edenic then $n+1$ is a perfect square:
--   $$n + 1 = p(p+2) + 1 = (p+1)^2.$$
--
--   So every Edenic semiprime sits exactly one below a square, with root $p+1$ — the arithmetic reason the integer square root of $n$ is $p$, i.e. $k-1$ where $k = p+1$.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_succ_is_square (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ k, n + 1 = k ^ 2 := by
  sorry
