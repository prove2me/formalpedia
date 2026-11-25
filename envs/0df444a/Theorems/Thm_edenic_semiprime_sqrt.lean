-- Prove2me | Theorems.Thm_edenic_semiprime_sqrt
-- name    : edenic_semiprime_sqrt
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T07:28:30.44628+00:00
-- url     : https://prove2.me/theorems/3c12e649-c23e-45a5-8d45-dda366fd4f94
-- title:
--   The integer square root of an Edenic semiprime
-- statement:
--   For every Edenic semiprime $n = p(p+2)$, taking $k = p + 1$ we have $n + 1 = k^2$ and
--   $$\lfloor \sqrt{n} \rfloor = k - 1 = p.$$
--
--   Since $n = k^2 - 1$, we have $(k-1)^2 = k^2 - 2k + 1 \le k^2 - 1 = n$ for $k \ge 1$, and $n < k^2$; the integer square root is therefore exactly $k - 1$.
--
--   **Formalization.** `Nat.eq_sub_of_add_eq` rewrites $n = k^2 - 1$; the two bounds go through `Nat.le_sqrt` and `Nat.sqrt_lt` with the expansions done by `ring`, and `omega` closes the sandwich.
--
--   **Reuse.** The integer square root of an Edenic semiprime recovers the smaller twin prime $p$ itself — inverting the family's defining map on its own range.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_sqrt (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ k, n + 1 = k ^ 2 ∧ Nat.sqrt n = k - 1 := by
  sorry
