-- Prove2me | Theorems.Thm_edenic_semiprime_five_dvd
-- name    : edenic_semiprime_five_dvd
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T06:10:59.192993+00:00
-- url     : https://prove2.me/theorems/5b56345f-7fc3-5475-a7e2-11d71892efff
-- title:
--   The Edenic cluster at 15 and 35
-- statement:
--   For an Edenic semiprime $n$,
--   $$5 \mid n \iff n = 15 \ \text{or}\ n = 35.$$
--
--   If $5 \mid p(p+2)$ then $5 \mid p$ or $5 \mid (p+2)$. The first gives $p = 5$ and $n = 5 \cdot 7 = 35$; the second gives $p + 2 = 5$, i.e. $p = 3$, and $n = 3 \cdot 5 = 15$.
--
--   These two numbers form the *cluster*: $15 = 3 \cdot 5$ and $35 = 5 \cdot 7$ share the hinge prime $5$, which belongs to both twin pairs $(3,5)$ and $(5,7)$. No other Edenic semiprime is divisible by $5$, and no prime other than $5$ can hinge two twin pairs (see `prime_in_two_twin_pairs`).
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_five_dvd (n : ℕ) (h : IsEdenicSemiprime n) :
    5 ∣ n ↔ n = 15 ∨ n = 35 := by
  sorry
