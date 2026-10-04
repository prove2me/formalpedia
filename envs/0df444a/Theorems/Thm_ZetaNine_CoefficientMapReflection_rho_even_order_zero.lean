-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapReflection_rho_even_order_zero
-- name    : ZetaNine.CoefficientMapReflection.rho_even_order_zero
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T19:17:27.194463+00:00
-- url     : https://prove2.me/theorems/b40f468c-1d43-46e1-a0fe-bb59afc285e7
-- title:
--   Even-order actual local coefficient totals vanish for even n
-- statement:
--   Let $n,s$ be natural numbers with $n$ even, $s$ even and $1\le s\le9$, and take any $W\in\mathbb Q[X]$. The total of the actual local coefficients satisfies
--
--   $$\rho_{n,s}(W)=\sum_{j=0}^{n}c^W_{n,j,s}=0.$$
--
--   No properness premise is needed. This includes $s=2,4,6,8$ and $n=0$. For $n=0,W=X^4$ all four even-order totals vanish, but the actual simple-pole total is one; this theorem does not claim that it vanishes.
-- source:
--   Zeta(9) actual finite reflection and coefficient-total research: missions/zeta9/research/coefficient-map-reflection-2026-10-03.md. Frozen source missions/zeta9/formalization/CoefficientMapReflection.lean, SHA256 8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707. This uses the actual finite product numerator/denominator, genuine weighted formal local coefficients and proved finite partial-fraction identity. Original declaration lines 278–291.

import Definitions.Def_ZetaNine_CoefficientMapReflection

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions

theorem ZetaNine.CoefficientMapReflection.rho_even_order_zero (n s : ℕ) (hn : Even n) (W : ℚ[X])
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hs : Even s) : rho n s W = 0:= by sorry
