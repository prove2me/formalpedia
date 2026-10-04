-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapSummation_actualSeries_hasSum_exactL
-- name    : ZetaNine.CoefficientMapSummation.actualSeries_hasSum_exactL
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T20:59:32.712985+00:00
-- url     : https://prove2.me/theorems/25ed8da5-f069-4864-95b4-3701e2ddec47
-- title:
--   The actual even-n strong-domain series has the exact odd-zeta sum
-- statement:
--   Let $n$ be even and $W\in\mathbb Q[X]$ satisfy $2n+2\operatorname{natdeg}W\le9(n+1)-2$. Then the actual positive rational sequence has genuine HasSum to $B_n(W)+\rho_{n,3}(W)\Re\zeta(3)+\rho_{n,5}(W)\Re\zeta(5)+\rho_{n,7}(W)\Re\zeta(7)+\rho_{n,9}(W)\Re\zeta(9)$. Both summability and actual rho cancellations are proved, without additional rho/summability/zeta inputs. The specialization $n=0,W=X^3$ gives the actual zeta3 series. In contrast, $n=0,W=X^4$ is outside the strong domain: its totalized Lean tsum is0 but it has no HasSum to any real number.
-- source:
--   Zeta(9) actual p9,q1,m=n,d0 infinite summation: missions/zeta9/research/coefficient-map-summation-2026-10-04.md. Frozen actual source SHA256 c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d. Actual numerator/pole products, shifted unit-denominator coefficient array, finite harmonic B/rho and actual strong-domain cancellation prove absolute convergence and the actual infinite L. Original declaration lines 259–266.

import Definitions.Def_ZetaNine_CoefficientMapSummation

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability

theorem ZetaNine.CoefficientMapSummation.actualSeries_hasSum_exactL (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) : HasSum (actualSeries n W) (exactL n W):= by sorry
