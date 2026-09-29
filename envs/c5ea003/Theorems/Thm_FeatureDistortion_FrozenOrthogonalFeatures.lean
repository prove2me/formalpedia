-- Prove2me | Theorems.Thm_FeatureDistortion_FrozenOrthogonalFeatures
-- name    : FeatureDistortion.FrozenOrthogonalFeatures
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-26T21:16:29.205985+00:00
-- url     : https://prove2.me/theorems/b4da1c99-5108-4b1b-ba79-b39517a6c0c6
-- title:
--   Lemma A.3 - Frozen features off the training span
-- statement:
--   Notation: $n = \#\{\text{training examples}\}$, $d$ is the input
--   dimension, $k$ the feature dimension, $X:\mathbb R^d\to\mathbb R^n$ the
--   data map, $Y$ the labels, $B:\mathbb R^d\to\mathbb R^k$ the features,
--   and $v\in\mathbb R^k$ the head. Adjoint means Euclidean transpose.
--   The loss is $\widehat L(v,B)=\|XB^\top v-Y\|^2$, with no normalization.
--   The probability model, when present, is explicitly specified below;
--   deterministic flow statements involve no random data assumption.
--
--   For every triple of natural numbers $n,d,k$, every continuous real-linear map $X:\mathbb R^d\to\mathbb R^n$, every $Y\in\mathbb R^n$, every $v_0\in\mathbb R^k$, every continuous real-linear map $B_0:\mathbb R^d\to\mathbb R^k$, and every pair of functions $a:\mathbb R\to\mathbb R^k$ and $F:\mathbb R\to\mathcal L(\mathbb R^d,\mathbb R^k)$, assume $a(0)=v_0$, $F(0)=B_0$, and that for every real $s\geq0$ derivatives within $[0,\infty)$ exist with values $\dot a(s)=-2F(s)X^*(XF(s)^*a(s)-Y)$ and $\dot F(s)=\bigl[x\mapsto-2\langle X^*(XF(s)^*a(s)-Y),x\rangle a(s)\bigr]$, the latter being a derivative in the space of continuous linear maps. Then for every real $t\geq0$ and every $x\in\mathbb R^d$ orthogonal to every vector $X^*z$ with $z\in\mathbb R^n$, one has $F(t)x=B_0x$. Thus the conclusion uses the orthogonal complement of $\{X^*z:z\in\mathbb R^n\}$. Adjoints and orthogonality are Euclidean. All dimensions may be zero; if this orthogonal complement is $\{0\}$ only $x=0$ is tested, and if $X=0$ every $x$ is tested. Existence of such curves and conditions at negative times are not asserted.
--
--   Formalization note: Direct source invariant, valid for arbitrary labels.
--   Source: Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Appendix A.2, PDF p. 24, Lemma A.3, equations (A.15)--(A.18). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.
-- source:
--   Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Appendix A.2, PDF p. 24, Lemma A.3, equations (A.15)--(A.18). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.

import Definitions.Def_FeatureDistortion_Model
open MeasureTheory Filter
open scoped Topology

namespace FeatureDistortion
theorem FrozenOrthogonalFeatures :
  ∀ (n d k : ℕ) (X : Vec d →L[ℝ] Vec n) (Y : Vec n)
    (v₀ : Vec k) (B₀ : Features d k) (γ : Trajectory d k),
    IsFineTuningFlow X Y v₀ B₀ γ →
    ∀ (t : ℝ), 0 ≤ t → ∀ x ∈ (rowSpace X)ᗮ, γ.features t x = B₀ x := by sorry
end FeatureDistortion
