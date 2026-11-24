-- Prove2me | Theorems.Thm_syracuse_cycle_eq_one_of_adjacent_period_sieve
-- name    : syracuse_cycle_eq_one_of_adjacent_period_sieve
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T07:49:25.315442+00:00
-- url     : https://prove2.me/theorems/8c4861ad-3c39-4370-9af6-c4bf7cdb5335
-- title:
--   Excluding Syracuse return times using adjacent orbit points
-- statement:
--   For the Syracuse map $T$ on natural numbers, let $m,p>0$ satisfy $T^p(m)=m$. If
--   $$158482p\le99991\left(\left\lfloor\frac{50508p}{31867}\right\rfloor+1\right),$$
--   then $m=1$. The test uses a lower bound of $2{,}887{,}463$ on the entries of a hypothetical nontrivial cycle, together with the fact that at least one of each pair of consecutive entries is at least $3{,}849{,}951$.
--
--   In the inclusive range $7621\le p\le100000$, 105 of the 830 lengths left by the [earlier period test](https://prove2.me/theorems/57ea67dc-32fb-4d0a-9680-8087c9ca9945) satisfy this exclusion, including $11917$. A total of 725 candidates survive both tests.
-- source:
--   Refinement of the previous period test https://prove2.me/theorems/57ea67dc-32fb-4d0a-9680-8087c9ca9945 using syracuse_cycle_adjacent_pair_budget and the verified baseline https://prove2.me/theorems/ef7628cb-d8e8-4cd0-a7f6-af252ae35745.

import Definitions.Def_syracuseStep
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Iterate

theorem syracuse_cycle_eq_one_of_adjacent_period_sieve (m p : ℕ) (hm : 0 < m) (hp : 0 < p) (hcyc : syracuseStep^[p] m = m)
    (hsieve : 158482 * p ≤ 99991 * (50508 * p / 31867 + 1)) : m = 1 := by sorry
