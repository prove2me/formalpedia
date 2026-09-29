-- Prove2me | Theorems.Thm_FeatureDistortion_OODRiskIdentity
-- name    : FeatureDistortion.OODRiskIdentity
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-26T21:17:15.034554+00:00
-- url     : https://prove2.me/theorems/0897b99a-57be-4fec-9323-936c9a09e4b2
-- title:
--   Lemma A.7 - OOD risk and the uncentered second moment
-- statement:
--   Notation: $n = \#\{\text{training examples}\}$, $d$ is the input
--   dimension, $k$ the feature dimension, $X:\mathbb R^d\to\mathbb R^n$ the
--   data map, $Y$ the labels, $B:\mathbb R^d\to\mathbb R^k$ the features,
--   and $v\in\mathbb R^k$ the head. Adjoint means Euclidean transpose.
--   The loss is $\widehat L(v,B)=\|XB^\top v-Y\|^2$, with no normalization.
--   The probability model, when present, is explicitly specified below;
--   deterministic flow statements involve no random data assumption.
--
--   For every pair of natural numbers $d,k$, every probability measure $\mu$ on $\mathbb R^d$ with integrable squared norm and $\langle z,\Sigma_\mu z\rangle>0$ for every nonzero $z\in\mathbb R^d$, every $w\in\mathbb R^d$, every $v\in\mathbb R^k$, and every continuous real-linear map $B:\mathbb R^d\to\mathbb R^k$, let $\Sigma_\mu=\int(x\otimes x)\,d\mu(x)$, where $(x\otimes x)(z)=\langle x,z\rangle x$, and let $e=B^*v-w$ and $L=\int\langle e,x\rangle^2\,d\mu(x)$. The assertion is the conjunction $L=\langle e,\Sigma_\mu e\rangle$, $(L=0\Longleftrightarrow B^*v=w)$, and $(0<L\Longleftrightarrow B^*v\neq w)$. The moment integral is operator-valued, the adjoint is Euclidean, and no mean-zero assumption is made. If $d=0$, the positivity hypothesis is vacuous, $e=0$, and $L=0$. If $k=0$, then $B^*v=0$, so the equivalences test whether $w=0$.
--
--   Formalization note: Source-derived risk identity and positive-definiteness consequences. The reversed inequality in (A.28) is excluded.
--   Source: Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Appendix A.2, PDF p. 26, Lemma A.7, equations (A.29)--(A.32). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.
-- source:
--   Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Appendix A.2, PDF p. 26, Lemma A.7, equations (A.29)--(A.32). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.

import Definitions.Def_FeatureDistortion_Model
open MeasureTheory Filter
open scoped Topology

namespace FeatureDistortion
theorem OODRiskIdentity :
  ∀ (d k : ℕ) (D : OODLaw d) (w : Vec d) (v : Vec k) (B : Features d k),
    oodLoss D w v B =
      inner ℝ (weights B v - w) (secondMoment D.measure (weights B v - w)) ∧
    (oodLoss D w v B = 0 ↔ weights B v = w) ∧
    (0 < oodLoss D w v B ↔ weights B v ≠ w) := by sorry
end FeatureDistortion
