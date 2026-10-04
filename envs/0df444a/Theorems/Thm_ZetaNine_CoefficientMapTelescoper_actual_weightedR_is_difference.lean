-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapTelescoper_actual_weightedR_is_difference
-- name    : ZetaNine.CoefficientMapTelescoper.actual_weightedR_is_difference
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-04T09:18:32.434394+00:00
-- url     : https://prove2.me/theorems/23c4b8f3-9745-4ed9-8719-931e672eb5a5
-- title:
--   The actual weighted rational function is the cumulative telescoper difference
-- statement:
--   Let natural $n$ be even and let $W\in\mathbb Q[X]$ satisfy the actual strong bound $2n+2\operatorname{natdeg}W\le9(n+1)-2$ and the genuine aggregate $F_n(W)=0$. At every rational regular point $t$ with $t+k\ne0$ for $0\le k\le n$, the actual weighted rational function equals $Q_{n,W}(t)-Q_{n,W}(t+1)$. Q is the actual cumulative local-coefficient function, not an assumed telescoper. These original domain conditions are retained. Without the strong bound, $n=0,W=X^4$ has zero aggregate and empty Q but the actual weighted value at1 is1, so the difference identity fails.
-- source:
--   Zeta(9) actual cumulative telescoper and numerator root factor: missions/zeta9/research/coefficient-map-telescoper-2026-10-04.md. Frozen actual source SHA256 8792e8ba5c6abcbdbe83b0aa4ffa1ab716fd05fac10da7275b86ab2f780fd121. Q is constructed from the genuine local coefficients. No rational-function difference or polynomial factorization is supplied as a premise. Original declaration lines 97–103.

import Definitions.Def_ZetaNine_CoefficientMapTelescoper

set_option autoImplicit false
open scoped BigOperators Topology
open Finset Polynomial Filter
open ZetaNine ZetaNine.CoefficientMapTelescoper ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate

theorem ZetaNine.CoefficientMapTelescoper.actual_weightedR_is_difference (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    CoefficientMap.weightedR n W t = telescoper n W t - telescoper n W (t + 1):= by sorry
