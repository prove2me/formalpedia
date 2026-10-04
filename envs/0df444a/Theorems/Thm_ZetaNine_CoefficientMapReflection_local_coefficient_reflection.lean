-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapReflection_local_coefficient_reflection
-- name    : ZetaNine.CoefficientMapReflection.local_coefficient_reflection
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T19:17:17.123478+00:00
-- url     : https://prove2.me/theorems/6c193bd2-e727-4992-8957-82c250a0b45c
-- title:
--   Actual local coefficient reflection at every pole for even n
-- statement:
--   Let $n,j,s$ be natural numbers, assume $n$ is even, $j\le n$, $1\le s\le9$, and take any $W\in\mathbb Q[X]$. The genuine local formal coefficients of the actual weighted rational function satisfy
--
--   $$c^W_{n,n-j,s}=(-1)^{s+1}c^W_{n,j,s}.$$
--
--   This follows from actual numerator/denominator reflection and the unit-denominator formal series identity, without properness, arbitrary coefficient data or a global coefficient-reflection hypothesis. The Even n condition is retained; no assertion for odd n is made.
-- source:
--   Zeta(9) actual finite reflection and coefficient-total research: missions/zeta9/research/coefficient-map-reflection-2026-10-03.md. Frozen source missions/zeta9/formalization/CoefficientMapReflection.lean, SHA256 8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707. This uses the actual finite product numerator/denominator, genuine weighted formal local coefficients and proved finite partial-fraction identity. Original declaration lines 258–276.

import Definitions.Def_ZetaNine_CoefficientMapReflection

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions

theorem ZetaNine.CoefficientMapReflection.local_coefficient_reflection (n j s : ℕ) (hn : Even n) (W : ℚ[X])
    (hj : j ≤ n) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    CoefficientMapJet.weightedLocalCoefficient n (n - j) s W =
      (-1 : ℚ) ^ (s + 1) * CoefficientMapJet.weightedLocalCoefficient n j s W:= by sorry
