-- Prove2me | Theorems.Thm_ZOGlobalLB_lemma_B_1
-- name    : ZOGlobalLB.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:47:29.477441+00:00
-- url     : https://prove2.me/theorems/cae76dfe-83d9-4cea-b149-83d3b94fb4ab
-- title:
--   Lemma B.1 — chain and activation derivatives
-- statement:
--   For the profiles of Appendix B, for every $w\in\mathbb R^T$:
--   $$|b_i|\le12,\quad\|Db_i\|\le20,\quad\|D^2b_i\|\le160,\quad\|DB_T\|\le24\sqrt T,\quad\|D^2B_T\|\le160,\quad\|Dg\|\le\tfrac{15}{2},\quad\|D^2g\|\le93 .$$
--   Every coordinate derivative of $B_T$ is nonpositive. If $i=\min\{j:|w_j|\le1\}$ exists, then $\partial_iB_T(w)\le-1$. The terms $b_i$, the chain $B_T$ and the activation vector $g=(g_1,\dots,g_T)$ are $C^2$.
--
--   These derivative bounds, uniform in $T$, give the global smoothness of the construction; the barrier $\partial_iB_T\le-1$ is the zero-chain's obstruction to stopping early.
--
--   Differences from the source:
--   - encoding: stages 1,…,T → indices 0,…,T−1 (Fin T); reason: Lean convention; b₁ is index 0
--   - reading: the profiles are C² (stated on p.36) → ContDiff ℝ 2 of b_i, B_T, g as conclusions; reason: makes the derivative bounds statements about genuine derivatives
--   - encoding: ‖D²f‖ bilinear operator norm; ∂_iB_T → norm of iteratedFDeriv ℝ 2; fderiv applied to the i-th basis vector; reason: same quantities
--   - generalization: T ≥ 1 (standing) → every T; reason: T = 0 is the empty chain, where every bound holds trivially; specializes to T ≥ 1
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Lemma B.1, p.37, (55)–(56); C² of the profiles, p.36

import Mathlib
import Definitions.Def_ZOGlobalLB_Profiles

namespace ZOGlobalLB

/-- **Lemma B.1 (Chain and activation derivatives).** Xia, Yuan, arXiv:2610.19652, Lemma B.1,
p.37, (55)–(56).

For the profiles of Appendix B: each chain term `b_i`, the chain `B_T` and the activation vector
`g = (g_1, …, g_T)` are `C²` on `ℝᵀ` (p.36), and
`|b_i| ≤ 12, ‖Db_i‖ ≤ 20, ‖D²b_i‖ ≤ 160, ‖DB_T‖ ≤ 24√T, ‖D²B_T‖ ≤ 160, ‖Dg‖ ≤ 15/2,
‖D²g‖ ≤ 93` (55). Every coordinate derivative of `B_T` is nonpositive, and if
`i = min{j : |w_j| ≤ 1}` exists then `∂_i B_T(w) ≤ -1` (56).

**Formalization Note.** Derivatives are Fréchet derivatives on `E T` with operator norms;
`‖D²f‖` is the norm of `iteratedFDeriv ℝ 2 f`, the bilinear operator norm. `C²` is stated first so
that the derivative bounds are about genuine derivatives. The coordinate derivative `∂_i B_T(w)` is
`fderiv ℝ chainBT w (EuclideanSpace.single i 1)`. Indices are 0-based. -/
theorem lemma_B_1 (T : ℕ) :
    (∀ i : Fin T, ContDiff ℝ 2 (fun w : E T => chainB w i)) ∧
    ContDiff ℝ 2 (chainBT (T := T)) ∧
    ContDiff ℝ 2 (gVec (T := T)) ∧
    ∀ w : E T,
      (∀ i : Fin T, |chainB w i| ≤ 12 ∧
        ‖fderiv ℝ (fun w : E T => chainB w i) w‖ ≤ 20 ∧
        ‖iteratedFDeriv ℝ 2 (fun w : E T => chainB w i) w‖ ≤ 160) ∧
      ‖fderiv ℝ chainBT w‖ ≤ 24 * Real.sqrt T ∧
      ‖iteratedFDeriv ℝ 2 chainBT w‖ ≤ 160 ∧
      ‖fderiv ℝ gVec w‖ ≤ 15 / 2 ∧
      ‖iteratedFDeriv ℝ 2 gVec w‖ ≤ 93 ∧
      (∀ i : Fin T, fderiv ℝ chainBT w (EuclideanSpace.single i 1) ≤ 0) ∧
      (∀ i : Fin T, |w i| ≤ 1 → (∀ j : Fin T, j < i → 1 < |w j|) →
        fderiv ℝ chainBT w (EuclideanSpace.single i 1) ≤ -1) := by sorry

end ZOGlobalLB
