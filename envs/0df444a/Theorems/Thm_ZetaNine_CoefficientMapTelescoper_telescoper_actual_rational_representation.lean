-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapTelescoper_telescoper_actual_rational_representation
-- name    : ZetaNine.CoefficientMapTelescoper.telescoper_actual_rational_representation
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-04T09:18:45.392972+00:00
-- url     : https://prove2.me/theorems/41d3c1e3-8972-4ea6-ad46-a5946ba63923
-- title:
--   The actual telescoper equals its genuine numerator over the pole product
-- statement:
--   For every $n\ge1$, rational polynomial $W$ and rational $t$ regular at every $t+k$, $0\le k<n$, the actual cumulative rational function equals $P_{n,W}(t)/M_n(t)^9$. Both the numerator and denominator are defined from the actual local coefficients and pole products. No Even n, strong bound, zero aggregate or preassigned rational identity is needed for this original endpoint.
-- source:
--   Zeta(9) actual cumulative telescoper and numerator root factor: missions/zeta9/research/coefficient-map-telescoper-2026-10-04.md. Frozen actual source SHA256 8792e8ba5c6abcbdbe83b0aa4ffa1ab716fd05fac10da7275b86ab2f780fd121. Q is constructed from the genuine local coefficients. No rational-function difference or polynomial factorization is supplied as a premise. Original declaration lines 257–269.

import Definitions.Def_ZetaNine_CoefficientMapTelescoper

set_option autoImplicit false
open scoped BigOperators Topology
open Finset Polynomial Filter
open ZetaNine ZetaNine.CoefficientMapTelescoper ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate

theorem ZetaNine.CoefficientMapTelescoper.telescoper_actual_rational_representation (n : ℕ) (hn1 : 1 ≤ n) (W : ℚ[X]) (t : ℚ)
    (hregular : ∀ k < n, t + (k : ℚ) ≠ 0) :
    telescoper n W t = (telescoperNumerator n W).eval t / (polePolynomial (n - 1)).eval t ^ 9:= by sorry
