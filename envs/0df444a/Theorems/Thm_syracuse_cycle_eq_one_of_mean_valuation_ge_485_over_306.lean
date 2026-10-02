-- Prove2me | Theorems.Thm_syracuse_cycle_eq_one_of_mean_valuation_ge_485_over_306
-- name    : syracuse_cycle_eq_one_of_mean_valuation_ge_485_over_306
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-01T22:53:10.689279+00:00
-- url     : https://prove2.me/theorems/a7d0c485-99df-4f66-b8fe-0c50634a1a34
-- title:
--   Positive Syracuse cycles with mean valuation at least 485/306 are trivial
-- statement:
--   Let $T(n)=\operatorname{oddpart}(3n+1)$ and write $v_2$ for the exponent of two. Suppose $m,p\in\mathbb N$, $m>0$, $p>0$ and $T^p(m)=m$. Define
--
--   $$K=\sum_{i=0}^{p-1}v_2(3T^i(m)+1).$$
--
--   If
--
--   $$485p\le306K,$$
--
--   then
--
--   $$m=1.$$
--
--   The supplied period need not be minimal, and the starting state need not be the cycle minimum. This sharpens the existing threshold $317/200$ to $485/306\approx1.58496732026$. It excludes an unbounded restricted family, not all cycles or divergent trajectories. The family below the new threshold remains an open obligation.
-- source:
--   Sharper rational specialization of the accepted global high-mean theorem https://prove2.me/theorems/da5c0141-3f01-4271-8ca2-cebe7d4d407e ; adapts accepted source submission4d6bff5f-ee5d-47a0-8867-67819f0e5206 with credit to its author and public community supports. Exact new certificate at B=2310000: (3B+1)^306 < 2^485 B^306. Minimum-product inequality: https://prove2.me/theorems/514577b7-9148-4a35-a0b2-80ac16b8b322 ; finite cycle-state baseline: https://prove2.me/theorems/73735589-bbad-479f-8d7e-375fd2f82875 ; periodic-reaches-one: https://prove2.me/theorems/a46524f0-afd4-4232-b74a-8a95d7ab31a5 . An elementary derived restriction, not a claim of a new proof of Collatz.

import Mathlib
import Definitions.Def_syracuseStep

set_option autoImplicit false

theorem syracuse_cycle_eq_one_of_mean_valuation_ge_485_over_306 (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hhigh : 485 * p ≤ 306 * (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] m + 1).factorization 2)) :
    m = 1 := by sorry
