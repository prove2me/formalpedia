-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapReflection_rho_one_zero_of_strong_proper
-- name    : ZetaNine.CoefficientMapReflection.rho_one_zero_of_strong_proper
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T19:17:36.046021+00:00
-- url     : https://prove2.me/theorems/8a1d6ae0-325a-4d46-acd5-448bcf59814c
-- title:
--   The actual simple-pole total vanishes under the stronger degree bound
-- statement:
--   For any natural $n$ and $W\in\mathbb Q[X]$, assume the genuine stronger degree condition $2n+2\operatorname{natdeg}W\le9(n+1)-2$. Then the actual simple-pole coefficient total vanishes:
--
--   $$\rho_{n,1}(W)=\sum_{j=0}^{n}c^W_{n,j,1}=0.$$
--
--   This uses the actual finite global polynomial partial-fraction identity and its coefficient at degree $9n+8$. It does not require Even n: every rational quartic is StrongProper for $n\ge1$, including $n=1$. Strict properness alone is insufficient: $n=0,W=X^4$ is proper but not StrongProper, with actual function $1/t$ and $\rho_{0,1}=1$. No infinite L-sum, convergence or original five-dimensional aggregate F inverse follows from this finite theorem.
-- source:
--   Zeta(9) actual finite reflection and coefficient-total research: missions/zeta9/research/coefficient-map-reflection-2026-10-03.md. Frozen source missions/zeta9/formalization/CoefficientMapReflection.lean, SHA256 8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707. This uses the actual finite product numerator/denominator, genuine weighted formal local coefficients and proved finite partial-fraction identity. Original declaration lines 352–363.

import Definitions.Def_ZetaNine_CoefficientMapReflection

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions

theorem ZetaNine.CoefficientMapReflection.rho_one_zero_of_strong_proper (n : ℕ) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) : rho n 1 W = 0:= by sorry
