-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_Supplement_matrix_concentration
-- name    : ZLIPPadding.Padding.Supplement.matrix_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:22:59.085031+00:00
-- url     : https://prove2.me/theorems/55dd04a0-77ef-4279-9e2a-6bfba088957a
-- title:
--   Lemma 4.6 — Euclidean operator-norm matrix concentration
-- statement:
--   Let $n\ge2$, $m\ge1$, $L=O\mathbb Z^n$, and prescribe $x\in S_m(L)$. For $N_x\ge1$ independent exact uniform shell samples $Y_i$, define $\widehat C_x=N_x^{-1}\sum_iY_iY_i^\top\langle x,Y_i\rangle^2$ and $C_x=\mathbb E[YY^\top\langle x,Y\rangle^2]$. For every real $t>0$,
--
--   $$\Pr\!\left[\|\widehat C_x-C_x\|_{\mathrm{op}}\ge t\right]\le2n\exp\!\left(-\frac{N_xt^2}{8m^6}\right).$$
--
--   The norm is the operator norm for Euclidean vectors, and the probability is the actual product sample law. This bound supplies the matrix-estimation error budget.
--
--   Differences from the source:
--   - encoding: independent ambient shell samples and Euclidean operator norm → the reused iid product law on integer shell coordinates and the norm of the Euclidean continuous linear map; reason: orthogonal transport preserves both the distribution and the operator norm
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 20 (PDF p. 21), Lemma 4.6

import Definitions.Def_ZLIPPadding_Padding_Supplement_Statistics

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal

theorem matrix_concentration (n m Nx : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m)
    (hNx : 0 < Nx) (O : RMat n) (hO : Orthogonal O)
    (μ : PMF (ZVec n)) (hμ : UniformOn μ (shell n m))
    (a : ZVec n) (ha : a ∈ shell n m) (t : ℝ) (ht : 0 < t) :
    prob (iid μ Nx) {zs | opNorm
      (empiricalC (rotate O (liftZ a)) (ambientBatch O zs) -
        momentC O m μ (rotate O (liftZ a))) ≥ t} ≤
      2*n*Real.exp (-(Nx : ℝ)*t^2/(8*(m : ℝ)^6)) := by sorry

end ZLIPPadding.Padding.Supplement
