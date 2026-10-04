-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMap_leadingPoleCoefficient_eq
-- name    : ZetaNine.CoefficientMap.leadingPoleCoefficient_eq
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T15:50:50.599483+00:00
-- url     : https://prove2.me/theorems/f7fc231d-18a3-4968-91f0-54f8ace0c892
-- title:
--   Closed formula for the actual highest cleared-pole coefficient
-- statement:
--   For natural numbers $n,j$ with $j\le n$, let $C_{n,j}$ be the value at $t=-j$ of the actual cleared expression $N_n(t)/Q_{n,j}(t)^9$, where $N_n(t)=n!^7\prod_{i=1}^{n}(t-i)\prod_{i=1}^{n}(t+n+i)$ and $Q_{n,j}(t)=\prod_{0\le k\le n,\ k\ne j}(t+k)$. Then
--
--   $$C_{n,j}=(-1)^{n+j}\binom{n}{j}^{9}\binom{n+j}{n}\binom{2n-j}{n}.$$
--
--   The coefficient is defined by the original products and clearing operation; this identity computes that value. It covers both endpoint poles $j=0,n$ and the case $n=0$, without a parity assumption.
-- source:
--   Zeta(9) research notes: missions/zeta9/research/coefficient-map-finite-entry-2026-10-03.md (actual product definitions and highest cleared-pole coefficient); underlying missions/zeta9/round5/research/arithmetic.md, equations (1), (5), and (6), specialized to p=9, one layer q=1, m=n. Frozen verified Lean source missions/zeta9/formalization/CoefficientMap.lean, SHA256 e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03. Original endpoint declaration lines 178–191.

import Definitions.Def_ZetaNine_CoefficientMap

set_option autoImplicit false
open Finset Polynomial
open ZetaNine.CoefficientMap

theorem ZetaNine.CoefficientMap.leadingPoleCoefficient_eq (n j : ℕ) (hj : j ≤ n) :
    leadingPoleCoefficient n j =
      (-1 : ℚ) ^ (n + j) * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ):= by sorry
