-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapAggregate_aggregate_zero_all_rho
-- name    : ZetaNine.CoefficientMapAggregate.aggregate_zero_all_rho
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T22:27:04.472977+00:00
-- url     : https://prove2.me/theorems/968f781f-c1a2-42aa-b0a4-be1ff3dbb93b
-- title:
--   All nine coefficient totals vanish under actual even strong-proper aggregate zero
-- statement:
--   Let $n$ be an even natural number, and let $W\in\mathbb Q[X]$ satisfy the actual stronger degree bound
--
--   $$2n+2\operatorname{natdeg}(W)+2\le9(n+1).$$
--
--   Assume the genuine five-output aggregate vanishes, $F_n(W)=0$, with coordinates $B_n(W),\rho_{n,3}(W),\rho_{n,5}(W),\rho_{n,7}(W),\rho_{n,9}(W)$. Then, for every natural order $s$ with $1\le s\le9$,
--
--   $$\rho_{n,s}(W)=\sum_{j=0}^n c^W_{n,j,s}=0.$$
--
--   These are the actual totals of the weighted local coefficients. Evenness and the stronger degree bound are retained. The conclusion concerns nine totals, not the individual local coefficient array, and it does not infer $W=0$. Strict properness alone would not suffice: $n=0,W=X^4$ has $F_0(X^4)=0$ but $\rho_{0,1}=1$; it is proper and fails the stronger bound.
-- source:
--   Zeta(9) genuine five rational coefficient outputs and quartic coordinates: missions/zeta9/research/coefficient-map-aggregate-2026-10-04.md. Frozen missions/zeta9/formalization/CoefficientMapAggregate.lean SHA256 e538a7310f81ce9ab6c5e07d4b8bd64bb70be7a899e28f085a2c8506a4ff2299. The coefficients are extracted from the actual weighted local formal series; B is the actual finite negative harmonic constant. Original declaration lines 156–165.

import Definitions.Def_ZetaNine_CoefficientMapAggregate

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapSummation ZetaNine.HarmonicStability

theorem ZetaNine.CoefficientMapAggregate.aggregate_zero_all_rho (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) : CoefficientMapFiniteSum.rho n s W = 0:= by sorry
