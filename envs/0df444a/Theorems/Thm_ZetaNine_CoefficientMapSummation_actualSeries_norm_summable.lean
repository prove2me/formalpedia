-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapSummation_actualSeries_norm_summable
-- name    : ZetaNine.CoefficientMapSummation.actualSeries_norm_summable
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T20:59:25.210701+00:00
-- url     : https://prove2.me/theorems/e202eaff-c82b-4d8b-b7a2-8b2896798987
-- title:
--   The actual positive weighted rational series is absolutely summable
-- statement:
--   For every natural $n$ and $W\in\mathbb Q[X]$ with $2n+2\operatorname{natdeg}W\le9(n+1)-2$, the genuine positive weighted sequence is absolutely summable: $\sum_{k\ge0}|f_{n,W}(k+1)|<\infty$. No Even n premise is required. The actual simple-pole coefficient total is proved zero from the stronger degree gap; its simple-pole terms are grouped into convergent differences. There is no supplied summability or cancellation hypothesis. Strict properness alone is insufficient: $n=0,W=X^4$ gives the divergent harmonic sequence.
-- source:
--   Zeta(9) actual p9,q1,m=n,d0 infinite summation: missions/zeta9/research/coefficient-map-summation-2026-10-04.md. Frozen actual source SHA256 c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d. Actual numerator/pole products, shifted unit-denominator coefficient array, finite harmonic B/rho and actual strong-domain cancellation prove absolute convergence and the actual infinite L. Original declaration lines 249–250.

import Definitions.Def_ZetaNine_CoefficientMapSummation

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability

theorem ZetaNine.CoefficientMapSummation.actualSeries_norm_summable (n : ℕ) (W : ℚ[X]) (hstrong : StrongProperMultiplier n W) :
    Summable (fun t : ℕ => ‖actualSeries n W t‖):= by sorry
