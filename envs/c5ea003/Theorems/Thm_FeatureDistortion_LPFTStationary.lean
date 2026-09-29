-- Prove2me | Theorems.Thm_FeatureDistortion_LPFTStationary
-- name    : FeatureDistortion.LPFTStationary
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-26T21:17:58.824338+00:00
-- url     : https://prove2.me/theorems/33de31c9-e4c9-41b7-8d03-b0184d059b5f
-- title:
--   Equations (A.214)--(A.218) - LP-FT stationarity
-- statement:
--   Notation: $n = \#\{\text{training examples}\}$, $d$ is the input
--   dimension, $k$ the feature dimension, $X:\mathbb R^d\to\mathbb R^n$ the
--   data map, $Y$ the labels, $B:\mathbb R^d\to\mathbb R^k$ the features,
--   and $v\in\mathbb R^k$ the head. Adjoint means Euclidean transpose.
--   The loss is $\widehat L(v,B)=\|XB^\top v-Y\|^2$, with no normalization.
--   The probability model, when present, is explicitly specified below;
--   deterministic flow statements involve no random data assumption.
--
--   For every triple of natural numbers $n,d,k$ and every choice of continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B_\star:\mathbb R^d\to\mathbb R^k$, real-linear isometric bijection $R:\mathbb R^k\to\mathbb R^k$, and $u_\star\in\mathbb R^k$, let $B_0=RB_\star$, $a_\star=Ru_\star$, $w_\star=B_\star^*u_\star$, $Y=Xw_\star$, $S=\{X^*z:z\in\mathbb R^n\}$, and $r=\dim_{\mathbb R}S$. Assume $0<k$, $k\leq r$, $r+k<d$, $B_\star B_\star^*=I_{\mathbb R^k}$, $u_\star\neq0$, and injectivity on $\mathbb R^k$ of $v\mapsto\Pi_S(B_0^*v)$ and of $v\mapsto\Pi_{S^\perp}(B_0^*v)$, with $\Pi$ denoting orthogonal projection. For every pair of functions $a:\mathbb R\to\mathbb R^k$ and $F:\mathbb R\to\mathcal L(\mathbb R^d,\mathbb R^k)$, if $a(0)=a_\star$, $F(0)=B_0$, and at every real $s\geq0$ their derivatives within $[0,\infty)$ are $\dot a(s)=-2F(s)X^*(XF(s)^*a(s)-Y)$ and $\dot F(s)=\bigl[x\mapsto-2\langle X^*(XF(s)^*a(s)-Y),x\rangle a(s)\bigr]$, with the second derivative taken in the space of continuous linear maps, then for every real $t\geq0$, $a(t)=a_\star$ and $F(t)=B_0$. All adjoints are Euclidean. These hypotheses exclude zero dimensions and require $n\geq k$ and $d\geq2k+1$. The proposition does not itself require such curves to exist, and their negative-time values are unconstrained.
--
--   Formalization note: Source-derived stationarity conclusion; uniqueness is needed in addition to vanishing gradients.
--   Source: Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Appendix A.7, PDF pp. 46--47, proof of Proposition 3.7, equations (A.214)--(A.218). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.
-- source:
--   Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Appendix A.7, PDF pp. 46--47, proof of Proposition 3.7, equations (A.214)--(A.218). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.

import Definitions.Def_FeatureDistortion_Model
open MeasureTheory Filter
open scoped Topology

namespace FeatureDistortion
theorem LPFTStationary :
  ∀ (n d k : ℕ) (P : Problem n d k), Admissible P →
    ∀ γ : Trajectory d k,
      IsFineTuningFlow P.data (labels P) (alignedHead P) (initialFeatures P) γ →
      ∀ t : ℝ, 0 ≤ t →
        γ.head t = alignedHead P ∧ γ.features t = initialFeatures P := by sorry
end FeatureDistortion
