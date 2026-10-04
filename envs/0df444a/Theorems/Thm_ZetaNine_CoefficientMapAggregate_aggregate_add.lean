-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapAggregate_aggregate_add
-- name    : ZetaNine.CoefficientMapAggregate.aggregate_add
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T22:26:49.908436+00:00
-- url     : https://prove2.me/theorems/698c5170-0bc3-479a-a014-bdc3dc5d4e4a
-- title:
--   Additivity of the actual five rational coefficient outputs
-- statement:
--   Let $n$ be any natural number and let $W,V\in\mathbb Q[X]$. For the actual aggregate
--
--   $$F_n(W)=(B_n(W),\rho_{n,3}(W),\rho_{n,5}(W),\rho_{n,7}(W),\rho_{n,9}(W)),$$
--
--   where every coefficient is extracted from the genuine weighted formal local series and $B_n$ is the finite negative harmonic constant, one has
--
--   $$F_n(W+V)=F_n(W)+F_n(V).$$
--
--   The equality is of all five rational coordinates, with pointwise addition. It holds for arbitrary rational polynomials and includes $n=0$ and zero polynomials, without an evenness, degree, properness or cancellation hypothesis.
-- source:
--   Zeta(9) genuine five rational coefficient outputs and quartic coordinates: missions/zeta9/research/coefficient-map-aggregate-2026-10-04.md. Frozen missions/zeta9/formalization/CoefficientMapAggregate.lean SHA256 e538a7310f81ce9ab6c5e07d4b8bd64bb70be7a899e28f085a2c8506a4ff2299. The coefficients are extracted from the actual weighted local formal series; B is the actual finite negative harmonic constant. Original declaration lines 64–67.

import Definitions.Def_ZetaNine_CoefficientMapAggregate

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapSummation ZetaNine.HarmonicStability

theorem ZetaNine.CoefficientMapAggregate.aggregate_add (n : ℕ) (W V : ℚ[X]) :
    aggregate n (W + V) = aggregate n W + aggregate n V:= by sorry
