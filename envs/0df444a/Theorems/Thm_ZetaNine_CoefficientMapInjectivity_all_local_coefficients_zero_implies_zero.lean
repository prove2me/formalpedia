-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapInjectivity_all_local_coefficients_zero_implies_zero
-- name    : ZetaNine.CoefficientMapInjectivity.all_local_coefficients_zero_implies_zero
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T17:12:41.558869+00:00
-- url     : https://prove2.me/theorems/6d9445a4-3353-476d-a21f-6a1875fda71d
-- title:
--   Zero actual local coefficients force a proper multiplier to vanish
-- statement:
--   Let $n\ge0$ be natural and $W\in\mathbb Q[X]$. Assume $2n+2\deg W<9(n+1)$. Take the actual coefficients $c^W_{n,j,s}=[z^{9-s}](N_{n,j}(D_{n,j}^{9})^{-1}W((z-j)(z-j+n)))$ in $\mathbb Q[[z]]$, where $N_{n,j}$ and $D_{n,j}$ are the genuine shifted numerator and erased pole-factor denominator. If $c^W_{n,j,s}=0$ for every $0\le j\le n$ and $1\le s\le9$, then $$W=0.$$ This is the zero-kernel criterion for the complete actual local array in the strict proper domain. It does not concern only five aggregated zeta/constant outputs or assert their injectivity.
-- source:
--   Zeta(9) finite proper-domain local coefficient-array research: missions/zeta9/research/coefficient-map-injectivity-2026-10-03.md. Frozen actual Lean source missions/zeta9/formalization/CoefficientMapInjectivity.lean, SHA256 ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095; uses genuine Base/Jet products and formal local jets. This concerns the complete (n+1) by 9 array, not the original five aggregated F outputs. Original declaration lines 180–190.

import Definitions.Def_ZetaNine_CoefficientMapInjectivity

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapInjectivity

theorem ZetaNine.CoefficientMapInjectivity.all_local_coefficients_zero_implies_zero (n : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (hzero : AllLocalCoefficientsZero n W) : W = 0:= by sorry
