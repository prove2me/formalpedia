-- Prove2me | Theorems.Thm_edenic_semiprime_ge_15
-- name    : edenic_semiprime_ge_15
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T06:11:01.647213+00:00
-- url     : https://prove2.me/theorems/1924d704-a2c8-4128-903b-7209c9de2c1c
-- title:
--   Edenic semiprimes are at least 15
-- statement:
--   Every Edenic semiprime satisfies $n \ge 15$.
--
--   The smaller member $p$ of the twin pair cannot be $2$, since $p + 2 = 4$ is composite; hence $p \ge 3$ and
--   $$n = p(p+2) \ge 3 \cdot 5 = 15.$$
--
--   So the family begins exactly at $15 = 3 \cdot 5$, and $15$ is indeed Edenic.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_ge_15 (n : ℕ) (h : IsEdenicSemiprime n) : 15 ≤ n := by
  sorry
