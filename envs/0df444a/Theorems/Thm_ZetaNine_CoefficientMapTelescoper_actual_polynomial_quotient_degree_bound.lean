-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapTelescoper_actual_polynomial_quotient_degree_bound
-- name    : ZetaNine.CoefficientMapTelescoper.actual_polynomial_quotient_degree_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-04T09:18:48.572388+00:00
-- url     : https://prove2.me/theorems/9e49b2d8-4a51-4bfd-b449-d665b5e5fc6d
-- title:
--   The actual zero-aggregate numerator has the full root factor and bounded quotient
-- statement:
--   Let $n\ge1$ be even, and let rational $W$ satisfy the actual strong bound and genuine $F_n(W)=0$. There exists rational polynomial $H$ such that the actual numerator $P_{n,W}=P_{0,n}H$ and $\operatorname{natdeg}H\le7n-3$. The actual $P_{0,n}$ has $2n+2$ distinct nodes $1,\ldots,n+1,-n,\ldots,-2n$. Their vanishing and divisibility are proved from the actual telescoper, regular nodes and finite/infinite sum identities; they are not extra assumptions. The zero-numerator case is included. Kernel triviality, inverse bounds and irrationality are separate results.
-- source:
--   Zeta(9) actual cumulative telescoper and numerator root factor: missions/zeta9/research/coefficient-map-telescoper-2026-10-04.md. Frozen actual source SHA256 8792e8ba5c6abcbdbe83b0aa4ffa1ab716fd05fac10da7275b86ab2f780fd121. Q is constructed from the genuine local coefficients. No rational-function difference or polynomial factorization is supplied as a premise. Original declaration lines 385–395.

import Definitions.Def_ZetaNine_CoefficientMapTelescoper

set_option autoImplicit false
open scoped BigOperators Topology
open Finset Polynomial Filter
open ZetaNine ZetaNine.CoefficientMapTelescoper ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate

theorem ZetaNine.CoefficientMapTelescoper.actual_polynomial_quotient_degree_bound (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) :
    ∃ H : ℚ[X], telescoperNumerator n W = rootPolynomial n * H ∧ H.natDegree ≤ 7 * n - 3:= by sorry
