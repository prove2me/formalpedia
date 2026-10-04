-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapPartialFractions_candidate_local_coefficients
-- name    : ZetaNine.CoefficientMapPartialFractions.candidate_local_coefficients
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T18:10:03.558989+00:00
-- url     : https://prove2.me/theorems/20e45c17-4aac-4a4c-86cb-45f107407ff5
-- title:
--   The actual partial-fraction candidate matches every local coefficient
-- statement:
--   Let $n,j,s$ be natural numbers, $j\le n$, $1\le s\le9$, and let $W\in\mathbb Q[X]$ be arbitrary. Let $c^W_{n,j,s}$ be the actual coefficient of $z^{9-s}$ in the genuine weighted local formal quotient. Construct $P_n^W$ from these actual coefficients by $\sum_{i=0}^{n}\sum_{r=1}^{9}c^W_{n,i,r}(D^*_{n,i})^9(X+i)^{9-r}$, where $D^*_{n,i}=\prod_{k\ne i}(X+k)$. Its cleared candidate local series satisfies
--
--   $$[z^{9-s}]\bigl(P_n^W(z-j)(D_{n,j}(z)^9)^{-1}\bigr)=c^W_{n,j,s}.$$
--
--   This is a genuine all-nine local coefficient match. It needs neither strict properness nor a global partial-fraction identity as an assumption. It remains valid when the multiplier is outside the proper domain.
-- source:
--   Zeta(9) actual finite global partial-fraction research: missions/zeta9/research/coefficient-map-partial-fractions-2026-10-03.md. Frozen Lean source missions/zeta9/formalization/CoefficientMapPartialFractions.lean, SHA256 eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a. The original actual Base/Jet/Injectivity finite products and local formal coefficients are used throughout. Original declaration lines 227–231.

import Definitions.Def_ZetaNine_CoefficientMapPartialFractions

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapInjectivity

theorem ZetaNine.CoefficientMapPartialFractions.candidate_local_coefficients (n j s : ℕ) (W : ℚ[X]) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    PowerSeries.coeff (9 - s) (candidateClearedSeries n j W) =
      CoefficientMapJet.weightedLocalCoefficient n j s W:= by sorry
