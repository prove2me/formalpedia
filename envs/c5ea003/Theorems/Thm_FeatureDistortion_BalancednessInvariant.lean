-- Prove2me | Theorems.Thm_FeatureDistortion_BalancednessInvariant
-- name    : FeatureDistortion.BalancednessInvariant
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-26T21:17:02.507382+00:00
-- url     : https://prove2.me/theorems/6d33a532-3c6f-4f48-a99b-fb04c3b4a497
-- title:
--   Lemma A.4 - Balancedness along fine-tuning
-- statement:
--   Notation: $n = \#\{\text{training examples}\}$, $d$ is the input
--   dimension, $k$ the feature dimension, $X:\mathbb R^d\to\mathbb R^n$ the
--   data map, $Y$ the labels, $B:\mathbb R^d\to\mathbb R^k$ the features,
--   and $v\in\mathbb R^k$ the head. Adjoint means Euclidean transpose.
--   The loss is $\widehat L(v,B)=\|XB^\top v-Y\|^2$, with no normalization.
--   The probability model, when present, is explicitly specified below;
--   deterministic flow statements involve no random data assumption.
--
--   For every triple of natural numbers $n,d,k$, every continuous real-linear map $X:\mathbb R^d\to\mathbb R^n$, every $Y\in\mathbb R^n$, every $v_0\in\mathbb R^k$, every continuous real-linear map $B_0:\mathbb R^d\to\mathbb R^k$, and every pair of functions $a:\mathbb R\to\mathbb R^k$ and $F:\mathbb R\to\mathcal L(\mathbb R^d,\mathbb R^k)$, assume $a(0)=v_0$, $F(0)=B_0$, and that at every real $s\geq0$ the derivatives within $[0,\infty)$ are $\dot a(s)=-2F(s)X^*(XF(s)^*a(s)-Y)$ and $\dot F(s)=\bigl[x\mapsto-2\langle X^*(XF(s)^*a(s)-Y),x\rangle a(s)\bigr]$, with the latter derivative in the space of continuous linear maps. Then for every real $t\geq0$, $a(t)a(t)^{\mathsf T}-F(t)F(t)^*=v_0v_0^{\mathsf T}-B_0B_0^*$ as endomorphisms of $\mathbb R^k$: for every $z\in\mathbb R^k$, $\langle a(t),z\rangle a(t)-F(t)F(t)^*z=\langle v_0,z\rangle v_0-B_0B_0^*z$. Adjoints are Euclidean. No normalization or zero initial balance is assumed. Zero dimensions are allowed; for $k=0$ this is equality of the sole endomorphism of the zero space. The assertion is conditional on these curves and concerns nonnegative times only.
--
--   Formalization note: Direct source invariant, without an initial normalization assumption.
--   Source: Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Appendix A.2, PDF p. 24, Lemma A.4, equations (A.19)--(A.20). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.
-- source:
--   Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Appendix A.2, PDF p. 24, Lemma A.4, equations (A.19)--(A.20). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.

import Definitions.Def_FeatureDistortion_Model
open MeasureTheory Filter
open scoped Topology

namespace FeatureDistortion
theorem BalancednessInvariant :
  ∀ (n d k : ℕ) (X : Vec d →L[ℝ] Vec n) (Y : Vec n)
    (v₀ : Vec k) (B₀ : Features d k) (γ : Trajectory d k),
    IsFineTuningFlow X Y v₀ B₀ γ →
    ∀ t : ℝ, 0 ≤ t → balance (γ.head t) (γ.features t) = balance v₀ B₀ := by sorry
end FeatureDistortion
