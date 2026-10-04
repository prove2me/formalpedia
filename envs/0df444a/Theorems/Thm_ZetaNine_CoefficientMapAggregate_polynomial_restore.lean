-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapAggregate_polynomial_restore
-- name    : ZetaNine.CoefficientMapAggregate.polynomial_restore
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T22:26:51.130983+00:00
-- url     : https://prove2.me/theorems/6d601e77-6dc4-4529-9542-673ee50ebbc2
-- title:
--   Exact recovery of every rational quartic from its five coefficients
-- statement:
--   Let $W\in\mathbb Q[X]$ have natural degree at most four. Write $\pi(W)_i=[X^i]W$ for $0\le i\le4$, and define $C(a)=\sum_{i=0}^4 a_iX^i$ for a rational five-coordinate vector $a$. Then
--
--   $$C(\pi(W))=W.$$
--
--   This recovers the actual polynomial from its five coefficients, including the zero polynomial, constants and nonmonic quartics. The degree bound is essential. It is a statement about quartic coordinates and does not assert that the aggregate $F_n$ has an inverse.
-- source:
--   Zeta(9) genuine five rational coefficient outputs and quartic coordinates: missions/zeta9/research/coefficient-map-aggregate-2026-10-04.md. Frozen missions/zeta9/formalization/CoefficientMapAggregate.lean SHA256 e538a7310f81ce9ab6c5e07d4b8bd64bb70be7a899e28f085a2c8506a4ff2299. The coefficients are extracted from the actual weighted local formal series; B is the actual finite negative harmonic constant. Original declaration lines 131–136.

import Definitions.Def_ZetaNine_CoefficientMapAggregate

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapSummation ZetaNine.HarmonicStability

theorem ZetaNine.CoefficientMapAggregate.polynomial_restore (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    coordinatePolynomial (polynomialCoordinates W) = W:= by sorry
