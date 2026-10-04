-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMap_clear_highest_pole
-- name    : ZetaNine.CoefficientMap.clear_highest_pole
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T15:50:43.370176+00:00
-- url     : https://prove2.me/theorems/ca2e0aab-8e1d-4199-980c-edc10cd4eabb
-- title:
--   Clearing the actual highest pole at every regular point
-- statement:
--   Let $n,j$ be natural numbers with $j\le n$. Define $N_n(t)=n!^7\prod_{i=1}^{n}(t-i)\prod_{i=1}^{n}(t+n+i)$, $Q_n(t)=\prod_{k=0}^{n}(t+k)$ and $R_n(t)=N_n(t)/Q_n(t)^9$. Let $Q_{n,j}$ omit the factor $t+j$, and write $\widetilde R_{n,j}=N_n/Q_{n,j}^9$. At every rational point $t$ satisfying $t+k\ne0$ for all $0\le k\le n$,
--
--   $$R_n(t)(t+j)^9=\widetilde R_{n,j}(t).$$
--
--   This identifies the actual cleared expression on the regular domain. It is a finite clearing identity; evaluation of the uncleared rational function at a pole is not used as a coefficient.
-- source:
--   Zeta(9) research notes: missions/zeta9/research/coefficient-map-finite-entry-2026-10-03.md (actual product definitions and highest cleared-pole coefficient); underlying missions/zeta9/round5/research/arithmetic.md, equations (1), (5), and (6), specialized to p=9, one layer q=1, m=n. Frozen verified Lean source missions/zeta9/formalization/CoefficientMap.lean, SHA256 e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03. Original endpoint declaration lines 75–85.

import Definitions.Def_ZetaNine_CoefficientMap

set_option autoImplicit false
open Finset Polynomial
open ZetaNine.CoefficientMap

theorem ZetaNine.CoefficientMap.clear_highest_pole (n j : ℕ) (hj : j ≤ n) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    actualR n t * (t + j) ^ 9 = clearedR n j t:= by sorry
