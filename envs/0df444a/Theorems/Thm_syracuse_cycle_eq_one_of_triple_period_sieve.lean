-- Prove2me | Theorems.Thm_syracuse_cycle_eq_one_of_triple_period_sieve
-- name    : syracuse_cycle_eq_one_of_triple_period_sieve
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T07:57:53.740431+00:00
-- url     : https://prove2.me/theorems/93fca028-3ab4-4bf0-ae35-499a41a0af27
-- title:
--   A Syracuse period exclusion from three consecutive orbit entries
-- statement:
--   For the Syracuse map $T$ and positive integers $m,p$ such that $T^p(m)=m$, put $L=\lfloor50508p/31867\rfloor+1$. If
--   $$110735p\le69866L,$$
--   then $m=1$. The test follows from a bound for three consecutive entries of a closed orbit. For $7621\le p\le100000$, it rules out 19 of the 725 lengths still admissible under the [adjacent-pair test](https://prove2.me/theorems/8c4861ad-3c39-4370-9af6-c4bf7cdb5335), leaving 706 candidates. For example, it excludes $p=12582$.
-- source:
--   Corollary of syracuse_cycle_three_consecutive_entries_budget and the verified lower cutoff https://prove2.me/theorems/ef7628cb-d8e8-4cd0-a7f6-af252ae35745. Refines the adjacent-pair period test.

import Definitions.Def_syracuseStep
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Iterate

theorem syracuse_cycle_eq_one_of_triple_period_sieve (m p : ℕ) (hm : 0 < m) (hp : 0 < p) (hcyc : syracuseStep^[p] m = m)
    (hsieve : 110735 * p ≤ 69866 * (50508 * p / 31867 + 1)) : m = 1 := by sorry
