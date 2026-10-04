-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapPartialFractions_actual_global_polynomial_partial_fractions
-- name    : ZetaNine.CoefficientMapPartialFractions.actual_global_polynomial_partial_fractions
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T18:10:21.366286+00:00
-- url     : https://prove2.me/theorems/0a3beccc-45c4-43dd-a023-16d5c4a9d849
-- title:
--   Exact global polynomial identity from actual local coefficients
-- statement:
--   For any natural $n$ and $W\in\mathbb Q[X]$, assume the strict proper-degree condition $2n+2\operatorname{natdeg}W<9(n+1)$. With $N_n(X)=n!^7\prod_{i=1}^{n}(X-i)(X+n+i)$, $U_n(X)=X(X+n)$ and the actual formal local coefficients $c^W_{n,j,s}$, one has
--
--   $$N_n(X)W(U_n(X))=\sum_{j=0}^{n}\sum_{s=1}^{9}c^W_{n,j,s}\left(\prod_{0\le k\le n,\ k\ne j}(X+k)\right)^9(X+j)^{9-s}.$$
--
--   This is an exact polynomial identity for the actual numerator and actual local coefficient candidate, including $n=0$. Strict properness is essential: at $n=0,W=X^5$ the actual numerator is $X^{10}$ while the nine-order candidate is zero, so the identity would fail without the condition.
-- source:
--   Zeta(9) actual finite global partial-fraction research: missions/zeta9/research/coefficient-map-partial-fractions-2026-10-03.md. Frozen Lean source missions/zeta9/formalization/CoefficientMapPartialFractions.lean, SHA256 eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a. The original actual Base/Jet/Injectivity finite products and local formal coefficients are used throughout. Original declaration lines 264–280.

import Definitions.Def_ZetaNine_CoefficientMapPartialFractions

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapInjectivity

theorem ZetaNine.CoefficientMapPartialFractions.actual_global_polynomial_partial_fractions (n : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) : weightedNumerator n W = partialNumerator n W:= by sorry
