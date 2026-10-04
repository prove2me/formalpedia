-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapSummation_original_integer_quartic_exact_infinite_L
-- name    : ZetaNine.CoefficientMapSummation.original_integer_quartic_exact_infinite_L
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T20:59:39.730977+00:00
-- url     : https://prove2.me/theorems/2de22270-2e72-4a2a-8279-109158a6bc9d
-- title:
--   The original even-n integer-quartic weighted series has its exact infinite sum
-- statement:
--   For every even integer $n\ge2$ and integer polynomial $W\in\mathbb Z[X]$ with degree at most4, cast its coefficients to $\mathbb Q$ and form the original actual p9,q1,m=n,d0 weighted rational function. The genuine positive sequence has HasSum to its exact $B+\rho_3\Re\zeta(3)+\rho_5\Re\zeta(5)+\rho_7\Re\zeta(7)+\rho_9\Re\zeta(9)$ linear form. The stronger degree bound is proved from the stated quartic/even-n domain. Integer W is not a claim that every rational local coefficient or full linear form is an integer. General parameters, inverse denominator heights, a small nonzero integer-form sequence, J and irrationality are separate obligations.
-- source:
--   Zeta(9) actual p9,q1,m=n,d0 infinite summation: missions/zeta9/research/coefficient-map-summation-2026-10-04.md. Frozen actual source SHA256 c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d. Actual numerator/pole products, shifted unit-denominator coefficient array, finite harmonic B/rho and actual strong-domain cancellation prove absolute convergence and the actual infinite L. Original declaration lines 272–275.

import Definitions.Def_ZetaNine_CoefficientMapSummation

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability

theorem ZetaNine.CoefficientMapSummation.original_integer_quartic_exact_infinite_L (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℤ[X]) (hW : W.natDegree ≤ 4) :
    HasSum (actualSeries n (W.map (Int.castRingHom ℚ))) (exactL n (W.map (Int.castRingHom ℚ))):= by sorry
