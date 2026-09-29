-- Prove2me | Theorems.Thm_FeatureDistortion_PerfectFeatureLPFTSeparation
-- name    : FeatureDistortion.PerfectFeatureLPFTSeparation
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-26T21:18:15.847585+00:00
-- url     : https://prove2.me/theorems/8363514c-bdbf-47ff-95e7-33aa1dabf2b1
-- title:
--   Proposition 3.7 - Perfect-feature LP-FT separation
-- statement:
--   Notation: $n = \#\{\text{training examples}\}$, $d$ is the input
--   dimension, $k$ the feature dimension, $X:\mathbb R^d\to\mathbb R^n$ the
--   data map, $Y$ the labels, $B:\mathbb R^d\to\mathbb R^k$ the features,
--   and $v\in\mathbb R^k$ the head. Adjoint means Euclidean transpose.
--   The loss is $\widehat L(v,B)=\|XB^\top v-Y\|^2$, with no normalization.
--   The probability model, when present, is explicitly specified below;
--   deterministic flow statements involve no random data assumption.
--
--   For every triple of natural numbers $n,d,k$, every choice of continuous real-linear maps $X:\mathbb R^d\to\mathbb R^n$ and $B_\star:\mathbb R^d\to\mathbb R^k$, real-linear isometric bijection $R:\mathbb R^k\to\mathbb R^k$, and $u_\star\in\mathbb R^k$, and every probability measure $\mu$ on $\mathbb R^d$ with integrable squared norm and $\langle z,\Sigma_\mu z\rangle>0$ for every nonzero $z\in\mathbb R^d$, where $\Sigma_\mu=\int(x\otimes x)\,d\mu(x)$ and $(x\otimes x)(z)=\langle x,z\rangle x$, let $B_0=RB_\star$, $a_\star=Ru_\star$, $w_\star=B_\star^*u_\star$, $Y=Xw_\star$, $S=\{X^*z:z\in\mathbb R^n\}$, and $r=\dim_{\mathbb R}S$. Assume $0<k$, $k\leq r$, $r+k<d$, $B_\star B_\star^*=I_{\mathbb R^k}$, $u_\star\neq0$, and injectivity on $\mathbb R^k$ of both $v\mapsto\Pi_S(B_0^*v)$ and $v\mapsto\Pi_{S^\perp}(B_0^*v)$, with $\Pi$ denoting orthogonal projection. For every real $\sigma>0$, four assertions hold together. Here a fine-tuning pair from $v_0$ means functions $a:\mathbb R\to\mathbb R^k$ and $F:\mathbb R\to\mathcal L(\mathbb R^d,\mathbb R^k)$ with $a(0)=v_0$, $F(0)=B_0$, and, at every real $t\geq0$, derivatives within $[0,\infty)$ equal to $\dot a(t)=-2F(t)X^*(XF(t)^*a(t)-Y)$ and $\dot F(t)=\bigl[x\mapsto-2\langle X^*(XF(t)^*a(t)-Y),x\rangle a(t)\bigr]$, the latter being a derivative in the space of continuous linear maps. A probing curve from $v_0$ means $b:\mathbb R\to\mathbb R^k$ with $b(0)=v_0$ and derivative within $[0,\infty)$ equal to $-2B_0X^*(XB_0^*b(t)-Y)$ at every real $t\geq0$. The four assertions are: (1) for every $v_0\in\mathbb R^k$ there exists a fine-tuning pair from $v_0$; (2) for every $v_0\in\mathbb R^k$ there exists a probing curve from $v_0$, and every probing curve from that $v_0$ tends to $a_\star$ in the Euclidean topology as $t\to+\infty$; (3) for every fine-tuning pair from $a_\star$ and every real $t\geq0$, $\int\langle F(t)^*a(t)-w_\star,x\rangle^2\,d\mu(x)=0$; and (4) for almost every $v_0$ under the pushforward of standard Gaussian measure on $\mathbb R^k$ by $z\mapsto\sigma z$, every fine-tuning pair from that $v_0$ satisfies $\int\langle F(t)^*a(t)-w_\star,x\rangle^2\,d\mu(x)>0$ for every real $t\geq0$. All adjoints are Euclidean. The exceptional null set in (4) is chosen before the universal quantifiers over pairs and times; this includes time zero and asserts positivity at each nonnegative real time, without a uniform positive lower bound or a statement about a limiting loss. The admissibility hypotheses exclude zero dimensions and require $n\geq k$ and $d\geq2k+1$. No conclusion is required for $\sigma\leq0$, and the curves have no conditions at negative times.
--
--   Formalization note: Source-derived Proposition 3.7 in the explicit nonzero-signal, identifiable perfect-feature regime, including flow existence and LP convergence. No uniform time-infimum, quantitative Theorem 3.3 constant, or imperfect-feature guarantee is claimed.
--   Source: Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47, equations (A.208)--(A.218). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.
-- source:
--   Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47, equations (A.208)--(A.218). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.

import Definitions.Def_FeatureDistortion_Model
open MeasureTheory Filter
open scoped Topology

namespace FeatureDistortion
theorem PerfectFeatureLPFTSeparation :
  ∀ (n d k : ℕ) (P : Problem n d k) (D : OODLaw d), Admissible P →
    ∀ σ : ℝ, 0 < σ →
      (∀ v₀ : Vec k, ∃ γ : Trajectory d k,
        IsFineTuningFlow P.data (labels P) v₀ (initialFeatures P) γ) ∧
      (∀ v₀ : Vec k,
        (∃ v : ℝ → Vec k, IsLinearProbingFlow P.data (labels P) v₀ (initialFeatures P) v) ∧
        ∀ v : ℝ → Vec k,
          IsLinearProbingFlow P.data (labels P) v₀ (initialFeatures P) v →
          Tendsto v atTop (𝓝 (alignedHead P))) ∧
      (∀ γ : Trajectory d k,
        IsFineTuningFlow P.data (labels P) (alignedHead P) (initialFeatures P) γ →
        ∀ t : ℝ, 0 ≤ t →
          oodLoss D (targetWeights P) (γ.head t) (γ.features t) = 0) ∧
      (∀ᵐ v₀ ∂gaussianHead k σ, ∀ γ : Trajectory d k,
        IsFineTuningFlow P.data (labels P) v₀ (initialFeatures P) γ →
        ∀ t : ℝ, 0 ≤ t →
          0 < oodLoss D (targetWeights P) (γ.head t) (γ.features t)) := by sorry
end FeatureDistortion
