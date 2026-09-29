-- Prove2me | Theorems.Thm_FedAvg_TunedConvexFedAvgConvergence
-- name    : FedAvg.TunedConvexFedAvgConvergence
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-22T23:54:46.035958+00:00
-- url     : https://prove2.me/theorems/f586b5c9-8aef-4dd3-8264-21347c35cca9
-- title:
--   Theorem 1 — Tuned-step Convergence (positive denominators)
-- statement:
--   ### Mathematical statement
--   Let $\tau,T\ge1$ and $D,\sigma,\zeta>0$. Choose
--   $$\eta=\min\left\{\frac1{4L},\frac{\sqrt M D}{\sqrt\tau\sqrt T\sigma},
--   \frac{D^{2/3}}{\tau^{2/3}T^{1/3}L^{1/3}\sigma^{2/3}},
--   \frac{D^{2/3}}{\tau T^{1/3}L^{1/3}\zeta^{2/3}}\right\}.$$
--   Then
--   $$\mathbb E[A]\le\frac{2LD^2}{\tau T}+\frac{2\sigma D}{\sqrt{M\tau T}}
--   +\frac{5L^{1/3}\sigma^{2/3}D^{4/3}}{\tau^{1/3}T^{2/3}}
--   +\frac{19L^{1/3}\zeta^{2/3}D^{4/3}}{T^{2/3}}.$$
--   Formalization note: direct source theorem restricted explicitly to the domain
--   where the printed equation (16) has positive denominators and positive step.
--   The separate constant-step target covers zero-parameter cases; no claim about
--   the literal tuned-step formula at zero denominators is made.
--
--   Source: Jianyu Wang et al., A Field Guide to Federated Optimization, arXiv:2107.06917v1, https://arxiv.org/abs/2107.06917v1; Section 6.1.2, PDF p. 41, Theorem 1, equations (16)–(17), in the positive-denominator regime.
--
--   ### Notation and probability model
--   There are $M\ge1$ clients with convex differentiable $L$-smooth functions
--   $F_i:\mathbb R^d\to\mathbb R$, $L>0$, and $F=M^{-1}\sum_iF_i$.
--   Let $x^\star$ minimize $F$, let $x_0$ be deterministic, and let
--   $D=\|x_0-x^\star\|$. The finite-dimensional space permits $d=0$.
--   On a standard Borel probability space $(\Omega,\mathcal A,\mathbb P)$,
--   $\mathcal F_{t\tau+k}$ contains the full history before step $(t,k)$.
--   All $M$ clients participate and use uniform weights. Starting from $x_0$,
--   $x_i^{t,k+1}=x_i^{t,k}-\eta g_i^{t,k}$; each subsequent round starts all
--   clients at the preceding round's terminal average.
--   The states are history-measurable and square integrable; gradients are measurable
--   at the next step and square integrable. Conditional on the current history,
--   client gradients are independent, have means $\nabla F_i(x_i^{t,k})$, and
--   their squared errors have expectations at most $\sigma^2$, with $\sigma\ge0$.
--   The uniform heterogeneity condition is $\|\nabla F_i(x)-\nabla F(x)\|\le\zeta$
--   for every $i,x$, with $\zeta\ge0$.
--   Write $\bar x^{t,k}=M^{-1}\sum_i x_i^{t,k}$,
--   $A_t=\tau^{-1}\sum_{k=1}^{\tau}(F(\bar x^{t,k})-F(x^\star))$, and
--   $A=T^{-1}\sum_{t=0}^{T-1}A_t$. Conditional statements hold almost surely.
--
--   Formalization note: the model makes the source's full-history stochastic-oracle
--   convention explicit. Independence is used in Appendix D.1 immediately after
--   equation (27), PDF p. 87. The moment/measurability and standard Borel conditions
--   are explicit analytic conventions. No convergence or intermediate bound is
--   assumed in the model. The source is Wang et al., *A Field Guide to Federated
--   Optimization*, Section 6.1.1, PDF p. 40, equations (11)–(14), and Section 6.1.2,
--   PDF p. 41, Theorem 1: https://arxiv.org/abs/2107.06917v1.
-- source:
--   Jianyu Wang et al., A Field Guide to Federated Optimization, arXiv:2107.06917v1, https://arxiv.org/abs/2107.06917v1; Section 6.1.2, PDF p. 41, Theorem 1, equations (16)–(17), in the positive-denominator regime.

import Definitions.Def_FedAvg_Model
open MeasureTheory
universe u

namespace FedAvg
theorem TunedConvexFedAvgConvergence :
  ∀ (d M : ℕ) (P : Problem d M) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (τ T : ℕ),
    0 < τ → 0 < T → 0 < distance P → 0 < P.σ → 0 < P.ζ →
    ∀ R : Run P μ τ T (optimizedStep P τ T),
      (∫ ω, avgLoss R ω ∂μ) ≤ optimizedRHS P τ T := by sorry
end FedAvg
