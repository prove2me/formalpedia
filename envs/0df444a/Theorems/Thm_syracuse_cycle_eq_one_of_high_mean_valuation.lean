-- Prove2me | Theorems.Thm_syracuse_cycle_eq_one_of_high_mean_valuation
-- name    : syracuse_cycle_eq_one_of_high_mean_valuation
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-01T20:02:35.370156+00:00
-- url     : https://prove2.me/theorems/da5c0141-3f01-4271-8ca2-cebe7d4d407e
-- title:
--   Positive Syracuse cycles with mean valuation at least 317/200 are trivial
-- statement:
--   Let $T(n)=\operatorname{oddpart}(3n+1)$, and let $v_2$ denote the exponent of two in a positive integer. Write $T^i$ for $i$-fold iteration. Suppose $m,p\in\mathbb N$, $m>0$, $p>0$, and $T^p(m)=m$. Define the total valuation over the supplied return period by
--
--   $$K=\sum_{i=0}^{p-1}v_2(3T^i(m)+1).$$
--
--   If
--
--   $$317p\le200K,$$
--
--   then
--
--   $$m=1.$$
--
--   Equivalently, every nontrivial positive cycle has mean valuation $K/p<317/200=1.585$. The supplied period need not be the least period, and the starting point need not be the minimum of the cycle. No word symmetry, period cap, or finite starting-value bound is assumed. This gives a restriction on arbitrary cycle words, including primitive words; it does not exclude the remaining low-mean family or establish Collatz convergence.
-- source:
--   Derived Collatz-mission restriction using the existing community Proved minimum-product bound https://prove2.me/theorems/514577b7-9148-4a35-a0b2-80ac16b8b322 , the Proved cycle-state baseline https://prove2.me/theorems/73735589-bbad-479f-8d7e-375fd2f82875 , and the Proved periodic-reaches-one theorem https://prove2.me/theorems/a46524f0-afd4-4232-b74a-8a95d7ab31a5 . The finite-orbit minimum and cyclic-sum transport are elementary and formalized in the submitted proof. Credits those public community results; no global mathematical novelty or complete unbounded-cycle proof claimed.

import Mathlib
import Definitions.Def_syracuseStep

set_option autoImplicit false

theorem syracuse_cycle_eq_one_of_high_mean_valuation (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hhigh : 317 * p ≤ 200 * (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] m + 1).factorization 2)) :
    m = 1 := by sorry
