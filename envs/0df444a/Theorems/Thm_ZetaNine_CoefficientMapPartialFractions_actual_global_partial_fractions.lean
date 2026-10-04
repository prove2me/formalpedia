-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapPartialFractions_actual_global_partial_fractions
-- name    : ZetaNine.CoefficientMapPartialFractions.actual_global_partial_fractions
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T18:10:26.923527+00:00
-- url     : https://prove2.me/theorems/d6bef8c0-d9cf-418e-ba46-2332ecca0c10
-- title:
--   Actual finite global partial fractions at every regular rational point
-- statement:
--   Let $n\ge0$ be natural, $W\in\mathbb Q[X]$, and assume $2n+2\operatorname{natdeg}W<9(n+1)$. Set $R_n(t)=n!^7\prod_{i=1}^{n}(t-i)(t+n+i)/(\prod_{k=0}^{n}(t+k))^9$, and take $c^W_{n,j,s}$ from its actual weighted local formal quotient. At every rational $t$ with $t+k\ne0$ for all $0\le k\le n$,
--
--   $$R_n(t)W(t(t+n))=\sum_{j=0}^{n}\sum_{s=1}^{9}\frac{c^W_{n,j,s}}{(t+j)^s}.$$
--
--   This is a finite exact partial-fraction equality at regular rational points. It does not assert infinite-sum convergence, vanishing of the simple-pole total, exact L, or injectivity/invertibility of the original aggregate F. At $n=0,W=X^4$ properness allows the simple pole $1/t$; $W=X^5$ is outside the proper domain.
-- source:
--   Zeta(9) actual finite global partial-fraction research: missions/zeta9/research/coefficient-map-partial-fractions-2026-10-03.md. Frozen Lean source missions/zeta9/formalization/CoefficientMapPartialFractions.lean, SHA256 eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a. The original actual Base/Jet/Injectivity finite products and local formal coefficients are used throughout. Original declaration lines 329–343.

import Definitions.Def_ZetaNine_CoefficientMapPartialFractions

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapInjectivity

theorem ZetaNine.CoefficientMapPartialFractions.actual_global_partial_fractions (n : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    CoefficientMap.weightedR n W t =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        CoefficientMapJet.weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s:= by sorry
