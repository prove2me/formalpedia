-- Prove2me | Theorems.Thm_syracuse_cycle_eq_one_of_eight_million_triple_sieve
-- name    : syracuse_cycle_eq_one_of_eight_million_triple_sieve
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T08:12:48.490082+00:00
-- url     : https://prove2.me/theorems/3532a743-e5d7-47ac-a080-29ee60e14315
-- title:
--   A Syracuse period sieve using the 8,388,608 cutoff
-- statement:
--   For a positive Syracuse periodic point $T^p(m)=m$ with $p>0$, set $L=\lfloor50508p/31867\rfloor+1$. If $116173p\le73297L$, then $m=1$. The proof combines the $2^{23}$ small-state exclusion with the cyclic three-entry budget. In the interval $7{,}621\le p\le100{,}000$, this removes 462 of the 706 lengths left by the previous three-entry test. The smallest of the remaining 244 lengths is 10,946.
-- source:
--   Applies syracuse_no_cycle_below_two_pow_twenty_three and the three-entry budget https://prove2.me/theorems/b41a66d1-5e1e-417d-8bb9-50b7baa86285.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_cycle_eq_one_of_eight_million_triple_sieve (m p : ℕ) (hm : 0 < m) (hp : 0 < p) (hcyc : syracuseStep^[p] m = m)
    (hsieve : 116173 * p ≤ 73297 * (50508 * p / 31867 + 1)) : m = 1 := by sorry
