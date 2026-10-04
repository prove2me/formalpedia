-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapInjectivity_fullLocalCoefficientMap_injective
-- name    : ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap_injective
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T17:12:49.798979+00:00
-- url     : https://prove2.me/theorems/1c1a796f-fcd9-49fa-b57b-721bbdf48ef6
-- title:
--   Injectivity of the full actual local coefficient array on the proper domain
-- statement:
--   For every natural $n$, restrict rational polynomials $W$ to $2n+2\deg W<9(n+1)$ and send them to the complete array of actual formal-jet coefficients $$(c^W_{n,j,s})_{0\le j\le n,\ 1\le s\le9}.$$ This map is injective: two multipliers in that domain with identical complete arrays are equal. Every coefficient is taken from the genuine shifted-product formal quotient, not abstract data. No surjectivity, inverse of the original five-dimensional aggregate F, or exact infinite L-sum is claimed.
-- source:
--   Zeta(9) finite proper-domain local coefficient-array research: missions/zeta9/research/coefficient-map-injectivity-2026-10-03.md. Frozen actual Lean source missions/zeta9/formalization/CoefficientMapInjectivity.lean, SHA256 ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095; uses genuine Base/Jet products and formal local jets. This concerns the complete (n+1) by 9 array, not the original five aggregated F outputs. Original declaration lines 217–226.

import Definitions.Def_ZetaNine_CoefficientMapInjectivity

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapInjectivity

theorem ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap_injective (n : ℕ) :
    Function.Injective (fun W : {W : ℚ[X] // ProperMultiplier n W} => fullLocalCoefficientMap n W.val):= by sorry
