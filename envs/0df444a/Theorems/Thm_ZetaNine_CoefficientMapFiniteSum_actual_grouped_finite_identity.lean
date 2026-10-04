-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapFiniteSum_actual_grouped_finite_identity
-- name    : ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T20:04:45.994108+00:00
-- url     : https://prove2.me/theorems/497fe537-7be9-4fad-8984-43229aafb166
-- title:
--   Actual finite rational sum with all nine harmonic terms retained
-- statement:
--   For natural $n,T$ and $W\in\mathbb Q[X]$, under the same actual strict proper condition $2n+2\operatorname{natdeg}W<9(n+1)$, the genuine finite sum satisfies
--
--   $$L_{n,T}(W)=B_n(W)+\sum_{s=1}^9\rho_{n,s}(W)H_T^{(s)}+E_{n,T}(W).$$
--
--   The simple-pole term $\rho_{n,1}(W)H_T^{(1)}$ is retained. No cancellation premise is introduced. For $n=0,W=X^4$, strict properness holds, $\rho_{0,1}=1$, $B_0=E_{0,T}=0$, and the actual finite sum is $H_T^{(1)}$. Therefore strict properness alone does not imply simple-pole cancellation or infinite L convergence. The separately conditional odd/no-simple wrappers are not submitted as public endpoints.
-- source:
--   Zeta(9) actual finite harmonic summation: missions/zeta9/research/coefficient-map-finite-sum-2026-10-03.md. Frozen missions/zeta9/formalization/CoefficientMapFiniteSum.lean SHA256 b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97. Coefficients are the actual weighted formal local jets of the p=9,q=1,m=n rational function, using the genuine finite global partial-fraction identity. Original declaration lines 91–109.

import Definitions.Def_ZetaNine_CoefficientMapFiniteSum

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.HarmonicStability

theorem ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) :
    finiteL n T W = constantTerm n W +
      (∑ s ∈ Icc 1 9, rho n s W * harmonicPower s T) + shiftedTail n T W:= by sorry
