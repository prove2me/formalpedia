-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMap_weightedLeadingPoleCoefficient_eq_even
-- name    : ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T15:50:57.956853+00:00
-- url     : https://prove2.me/theorems/970374db-a705-4462-9ace-d0a494c3672e
-- title:
--   Actual weighted highest-pole coefficient at every even order
-- statement:
--   Let $n,j$ be natural numbers, with $n$ even and $j\le n$, and let $W\in\mathbb Q[X]$ be any rational polynomial. Starting from the actual rational function $R_n(t)=N_n(t)/Q_n(t)^9$, multiply by $W(t(t+n))$. Define its highest cleared-pole value $C^W_{n,j}$ by evaluating $N_n(t)W(t(t+n))/Q_{n,j}(t)^9$ at $t=-j$. Then
--
--   $$C^W_{n,j}=(-1)^j\binom{n}{j}^{9}\binom{n+j}{n}\binom{2n-j}{n}\,W\bigl(-j(n-j)\bigr).$$
--
--   This computes the effect of the actual polynomial multiplier on the highest cleared-pole value. The multiplier is arbitrary, including the zero polynomial, and the weighted coefficient can be zero. The statement covers $n=0$ and does not assert a full Laurent expansion, a lower-coefficient map, or an infinite-sum identity.
-- source:
--   Zeta(9) research notes: missions/zeta9/research/coefficient-map-finite-entry-2026-10-03.md (actual product definitions and highest cleared-pole coefficient); underlying missions/zeta9/round5/research/arithmetic.md, equations (1), (5), and (6), specialized to p=9, one layer q=1, m=n. Frozen verified Lean source missions/zeta9/formalization/CoefficientMap.lean, SHA256 e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03. Original endpoint declaration lines 260–266.

import Definitions.Def_ZetaNine_CoefficientMap

set_option autoImplicit false
open Finset Polynomial
open ZetaNine.CoefficientMap

theorem ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even (n j : ℕ) (hn : Even n)
    (hj : j ≤ n) (W : ℚ[X]) :
    weightedLeadingPoleCoefficient n j W =
      (-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) *
          W.eval (-(j : ℚ) * (n - j : ℕ)):= by sorry
