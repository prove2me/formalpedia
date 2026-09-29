-- Prove2me | Theorems.Thm_FeatureDistortion_GradientFlowWellPosed
-- name    : FeatureDistortion.GradientFlowWellPosed
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-26T21:16:02.071741+00:00
-- url     : https://prove2.me/theorems/cb52de81-7632-49b8-b27e-c633723faaeb
-- title:
--   Equations (3.2)--(3.3) - Global gradient flows
-- statement:
--   Notation: $n = \#\{\text{training examples}\}$, $d$ is the input
--   dimension, $k$ the feature dimension, $X:\mathbb R^d\to\mathbb R^n$ the
--   data map, $Y$ the labels, $B:\mathbb R^d\to\mathbb R^k$ the features,
--   and $v\in\mathbb R^k$ the head. Adjoint means Euclidean transpose.
--   The loss is $\widehat L(v,B)=\|XB^\top v-Y\|^2$, with no normalization.
--   The probability model, when present, is explicitly specified below;
--   deterministic flow statements involve no random data assumption.
--
--   For every triple of natural numbers $n,d,k$, every continuous real-linear map $X:\mathbb R^d\to\mathbb R^n$, every $Y\in\mathbb R^n$, every $v_0\in\mathbb R^k$, and every continuous real-linear map $B_0:\mathbb R^d\to\mathbb R^k$, three assertions hold together. First, there exist functions $a:\mathbb R\to\mathbb R^k$ and $F:\mathbb R\to\mathcal L(\mathbb R^d,\mathbb R^k)$ with $a(0)=v_0$ and $F(0)=B_0$ such that for every real $t\geq0$ their derivatives within $[0,\infty)$ are $\dot a(t)=-2F(t)X^*(XF(t)^*a(t)-Y)$ and $\dot F(t)=\bigl[x\mapsto-2\langle X^*(XF(t)^*a(t)-Y),x\rangle a(t)\bigr]$, the latter being a derivative in the space of continuous linear maps. Second, for every two pairs $(a_1,F_1)$ and $(a_2,F_2)$ with those initial conditions and differential equations, $a_1(t)=a_2(t)$ and $F_1(t)=F_2(t)$ for every real $t\geq0$. Third, there exists $b:\mathbb R\to\mathbb R^k$ with $b(0)=v_0$ and derivative within $[0,\infty)$ equal to $-2B_0X^*(XB_0^*b(t)-Y)$ for every real $t\geq0$. Here $\mathcal L$ denotes continuous real-linear maps and $^*$ the Euclidean adjoint. The derivatives at zero are within the half-line. Values at negative times have no restrictions, and uniqueness of $b$ is not asserted. All dimensions may be zero, and no rank, normalization, or consistency hypotheses are imposed.
--
--   Formalization note: Formal ODE bridge for the source-backed parent; global existence and FT uniqueness are analytic obligations implicit in the source flow notation, not a separately numbered paper theorem.
--   Source: Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Section 3.1, PDF p. 6, equations (3.2)--(3.3). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.
-- source:
--   Kumar, Raghunathan, Jones, Ma, and Liang, Fine-Tuning can Distort Pretrained Features and Underperform Out-of-Distribution, ICLR 2022, https://arxiv.org/pdf/2202.10054v1. Section 3.1, PDF p. 6, equations (3.2)--(3.3). Source-backed parent: Section 3.4, PDF p. 10, Proposition 3.7, equations (3.10)--(3.11); Appendix A.7, PDF pp. 45--47.

import Definitions.Def_FeatureDistortion_Model
open MeasureTheory Filter
open scoped Topology

namespace FeatureDistortion
theorem GradientFlowWellPosed :
  ∀ (n d k : ℕ) (X : Vec d →L[ℝ] Vec n) (Y : Vec n)
    (v₀ : Vec k) (B₀ : Features d k),
    (∃ γ : Trajectory d k, IsFineTuningFlow X Y v₀ B₀ γ) ∧
    (∀ γ₁ γ₂ : Trajectory d k,
      IsFineTuningFlow X Y v₀ B₀ γ₁ → IsFineTuningFlow X Y v₀ B₀ γ₂ →
      ∀ t : ℝ, 0 ≤ t → γ₁.head t = γ₂.head t ∧ γ₁.features t = γ₂.features t) ∧
    (∃ v : ℝ → Vec k, IsLinearProbingFlow X Y v₀ B₀ v) := by sorry
end FeatureDistortion
