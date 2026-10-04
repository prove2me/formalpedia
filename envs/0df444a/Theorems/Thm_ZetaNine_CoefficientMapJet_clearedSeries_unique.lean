-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapJet_clearedSeries_unique
-- name    : ZetaNine.CoefficientMapJet.clearedSeries_unique
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T16:06:52.510501+00:00
-- url     : https://prove2.me/theorems/064cbef1-f817-40cb-b85b-29a79a5d5611
-- title:
--   Uniqueness of the actual cleared formal local series
-- statement:
--   For any natural numbers $n,j$, let $T_j(z)=z-j$, $N_{n,j}(z)=n!^7\prod_{i=1}^{n}(T_j(z)-i)\prod_{i=1}^{n}(T_j(z)+n+i)$ and $D_{n,j}(z)=\prod_{0\le k\le n,\ k\ne j}(T_j(z)+k)$. Let $S_{n,j}=N_{n,j}(D_{n,j}^9)^{-1}$ in $\mathbb Q[[z]]$. For every formal power series $S\in\mathbb Q[[z]]$,
--
--   $$S D_{n,j}^9=N_{n,j}\quad\Longrightarrow\quad S=S_{n,j}.$$
--
--   The actual denominator has nonzero constant coefficient, so this is the unique formal local quotient of the genuine shifted products. The uniqueness statement holds for all natural $j$; its application to a pole of the original rational function uses $j\le n$. No numerical evaluation or analytic convergence of the formal series is asserted.
-- source:
--   Zeta(9) research notes: missions/zeta9/research/coefficient-map-jet-2026-10-03.md (actual shifted numerator, cleared denominator, formal local quotient and all nine convolution orders); underlying missions/zeta9/round5/research/arithmetic.md, equation (5), specialized to p=9, one layer q=1, m=n. Frozen verified Lean source missions/zeta9/formalization/CoefficientMapJet.lean, SHA256 e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a; frozen actual Base source missions/zeta9/formalization/CoefficientMap.lean, SHA256 e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03. Original endpoint declaration lines 122–135.

import Definitions.Def_ZetaNine_CoefficientMapJet

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapJet

theorem ZetaNine.CoefficientMapJet.clearedSeries_unique (n j : ℕ) (S : PowerSeries ℚ)
    (hS : S * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
      (shiftedNumerator n j : PowerSeries ℚ)) : S = clearedSeries n j:= by sorry
