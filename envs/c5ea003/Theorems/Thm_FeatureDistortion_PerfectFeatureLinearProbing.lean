-- Prove2me | Theorems.Thm_FeatureDistortion_PerfectFeatureLinearProbing
-- name    : FeatureDistortion.PerfectFeatureLinearProbing
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-26T21:17:43.5473+00:00
-- url     : https://prove2.me/theorems/b2b69362-0943-4d2a-aec9-57116ca97645
-- title:
--   Proposition A.20 - Perfect-feature LP recovery
-- statement:
--   Notation: $n = \#\{\text{training examples}\}$, $d$ is the input
--   dimension, $k$ the feature dimension, $X:\mathbb R^d\to\mathbb R^n$ the
--   data map, $Y$ the labels, $B:\mathbb R^d\to\mathbb R^k$ the features,
--   and $v\in\mathbb R^k$ the head. Adjoint means Euclidean transpose.
--   The loss is $\widehat L(v,B)=\|XB^\top v-Y\|^2$, with no normalization.
--   The probability model, when present, is explicitly specified below;
--   deterministic flow statements involve no random data assumption.
--
--   For every triple of natural numbers $n,d,k$ and every choice of continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B_\star:\mathbb R^d\to\mathbb R^k$, real-linear isometric bijection $R:\mathbb R^k\to\mathbb R^k$, and $u_\star\in\mathbb R^k$, put $B_0=RB_\star$, $a_\star=Ru_\star$, $w_\star=B_\star^*u_\star$, $Y=Xw_\star$, $S=\{X^*z:z\in\mathbb R^n\}$, and $r=\dim_{\mathbb R}S$. Assume $0<k$, $k\leq r$, $r+k<d$, $B_\star B_\star^*=I_{\mathbb R^k}$, $u_\star\neq0$, and injectivity on $\mathbb R^k$ of both $v\mapsto\Pi_S(B_0^*v)$ and $v\mapsto\Pi_{S^\perp}(B_0^*v)$, where $\Pi$ denotes orthogonal projection. Then two assertions hold: for every $v\in\mathbb R^k$, $\|XB_0^*v-Y\|^2=0$ if and only if $v=a_\star$; and for every $v_0\in\mathbb R^k$ and every function $b:\mathbb R\to\mathbb R^k$ with $b(0)=v_0$ and derivative within $[0,\infty)$ equal to $-2B_0X^*(XB_0^*b(t)-Y)$ at every real $t\geq0$, $b(t)\to a_\star$ in the Euclidean topology as $t\to+\infty$. All adjoints are Euclidean. The hypotheses exclude zero dimensions and require $n\geq k$ and $d\geq2k+1$; if there are no qualifying data the implication is vacuous. Existence of $b$ is not asserted here, and its values at negative times are unconstrained.
--
--   Formalization note: Source-derived Proposition A.20 and its rotated-feature extension; convergence is a conclusion, with explicit identifiability assumptions.
--   Source: Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Appendix A.7, PDF pp. 45--46, Proposition A.20, equations (A.208)--(A.211), and the following rotation paragraph on PDF p. 46. Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.
-- source:
--   Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Appendix A.7, PDF pp. 45--46, Proposition A.20, equations (A.208)--(A.211), and the following rotation paragraph on PDF p. 46. Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.

import Definitions.Def_FeatureDistortion_Model
open MeasureTheory Filter
open scoped Topology

namespace FeatureDistortion
theorem PerfectFeatureLinearProbing :
  ∀ (n d k : ℕ) (P : Problem n d k), Admissible P →
    (∀ v : Vec k,
      trainingLoss P.data (labels P) v (initialFeatures P) = 0 ↔ v = alignedHead P) ∧
    (∀ (v₀ : Vec k) (v : ℝ → Vec k),
      IsLinearProbingFlow P.data (labels P) v₀ (initialFeatures P) v →
      Tendsto v atTop (𝓝 (alignedHead P))) := by sorry
end FeatureDistortion
