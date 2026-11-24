-- Prove2me | Theorems.Thm_collatz_smaller_merger_of_odd_run_divisibility
-- name    : collatz_smaller_merger_of_odd_run_divisibility
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T07:29:40.693802+00:00
-- url     : https://prove2.me/theorems/d4957fd8-6a25-4df3-bdab-d002245f16c4
-- title:
--   Smaller Collatz orbit mergers from odd runs of arbitrary length
-- statement:
--   Let $C$ send even integers to their halves and odd integers to three times their value plus one. Suppose $n$ is an odd natural number and $a,m$ are nonnegative integers satisfying
--   $$3\cdot2^{a+m}\le 3^m,\qquad 3^m\mid 2^a(3n+1)+1.$$
--   There is then a positive integer $k<n$ whose orbit satisfies
--   $$C^{2m+a}(k)=C(n)=3n+1.$$
--   Indeed, writing $q=(2^a(3n+1)+1)/3^m$, one may take $k=2^mq-1$. The exponents are unrestricted. This criterion also applies to odd multiples of three, where it witnesses a merger one step along the target orbit.
-- source:
--   Original merger criterion for https://prove2.me/theorems/2f2c89a6-40b8-4b55-81e9-679859a06e43. The odd-run identity for shortcut steps is also formalized as CollatzWork.oddRun, https://prove2.me/theorems/c8f74a85-42ec-403c-a523-4010d3c89522. Here two ordinary steps implement each odd shortcut.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_smaller_merger_of_odd_run_divisibility (n a m : ℕ) (hodd : n % 2 = 1)
    (hgain : 3 * 2 ^ (a + m) ≤ 3 ^ m)
    (hdiv : 3 ^ m ∣ 2 ^ a * (3 * n + 1) + 1) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ collatzStep^[2 * m + a] k = collatzStep n := by sorry
