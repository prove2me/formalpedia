-- Prove2me | Theorems.Thm_FedAvg_ConvexFedAvgConvergence
-- name    : FedAvg.ConvexFedAvgConvergence
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-22T23:53:47.06893+00:00
-- url     : https://prove2.me/theorems/db29e7cd-a4dd-4ca3-88d5-7a7118358524
-- title:
--   Theorem 1 — Convex FedAvg Convergence (constant step)
-- statement:
--   ### Mathematical statement
--   For $\tau,T\ge1$ and $0<\eta\le1/(4L)$,
--   $$\mathbb E[A]\le\frac{D^2}{2\eta\tau T}+\frac{\eta\sigma^2}{M}
--   +4\tau\eta^2L\sigma^2+18\tau^2\eta^2L\zeta^2.$$
--   Formalization note: direct source theorem, precisely equation (15). Zero noise,
--   zero heterogeneity, and zero initial distance are included. The quantity is
--   average post-update shadow loss, not a last-iterate guarantee.
--
--   Source: Jianyu Wang et al., A Field Guide to Federated Optimization, arXiv:2107.06917v1, https://arxiv.org/abs/2107.06917v1; Section 6.1.2, PDF p. 41, Theorem 1, equation (15).
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
--   Jianyu Wang et al., A Field Guide to Federated Optimization, arXiv:2107.06917v1, https://arxiv.org/abs/2107.06917v1; Section 6.1.2, PDF p. 41, Theorem 1, equation (15).

import Definitions.Def_FedAvg_Model
open MeasureTheory
universe u

namespace FedAvg
theorem ConvexFedAvgConvergence :
  ∀ (d M : ℕ) (P : Problem d M) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ T : ℕ) (η : ℝ),
    0 < τ → 0 < T → 0 < η → η ≤ 1 / (4 * P.L) →
    ∀ R : Run P μ τ T η, (∫ ω, avgLoss R ω ∂μ) ≤ convergenceRHS P τ T η := by sorry
end FedAvg
