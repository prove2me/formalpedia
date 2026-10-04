-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapFiniteSum_actual_finite_harmonic_identity
-- name    : ZetaNine.CoefficientMapFiniteSum.actual_finite_harmonic_identity
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T20:04:50.619365+00:00
-- url     : https://prove2.me/theorems/500f3668-d61c-42c7-adee-61ab5c3f742c
-- title:
--   Actual finite rational sum as a shifted harmonic double sum
-- statement:
--   Let $n,T$ be natural numbers and $W\in\mathbb Q[X]$. Assume the actual strict proper-degree condition $2n+2\operatorname{natdeg}W<9(n+1)$. Then
--
--   $$L_{n,T}(W)=\sum_{j=0}^n\sum_{s=1}^9c^W_{n,j,s}(H_{T+j}^{(s)}-H_j^{(s)}).$$
--
--   Every $c^W_{n,j,s}$ is extracted from the actual weighted local formal series. The genuine global rational partial fractions apply at every positive integer $t$, whose denominators $t+j$ are nonzero; only finite sums are exchanged. This includes $T=0$ and does not assume arbitrary coefficients, reflection, an infinite sum or convergence.
-- source:
--   Zeta(9) actual finite harmonic summation: missions/zeta9/research/coefficient-map-finite-sum-2026-10-03.md. Frozen missions/zeta9/formalization/CoefficientMapFiniteSum.lean SHA256 b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97. Coefficients are the actual weighted formal local jets of the p=9,q=1,m=n rational function, using the genuine finite global partial-fraction identity. Original declaration lines 53–89.

import Definitions.Def_ZetaNine_CoefficientMapFiniteSum

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.HarmonicStability

theorem ZetaNine.CoefficientMapFiniteSum.actual_finite_harmonic_identity (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) :
    finiteL n T W = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
      CoefficientMapJet.weightedLocalCoefficient n j s W *
        (harmonicPower s (T + j) - harmonicPower s j):= by sorry
