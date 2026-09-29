-- Prove2me | Theorems.Thm_FedAvg_PerRoundProgress
-- name    : FedAvg.PerRoundProgress
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-22T23:52:57.106171+00:00
-- url     : https://prove2.me/theorems/552d36ac-9286-4707-b476-9ab991279f06
-- title:
--   Lemma 1 — Per Round Progress
-- statement:
--   ### Mathematical statement
--   For $\tau,T\ge1$, $0<\eta\le1/(4L)$ and every $0\le t<T$,
--   $$\mathbb E[A_t\mid\mathcal F_{t\tau}]
--   \le\frac{\|\bar x^{t,0}-x^\star\|^2-
--   \mathbb E[\|\bar x^{t,\tau}-x^\star\|^2\mid\mathcal F_{t\tau}]}{2\eta\tau}
--   +\frac{\eta\sigma^2}{M}+\frac{L}{M\tau}
--   \sum_{i=1}^M\sum_{k=0}^{\tau-1}
--   \mathbb E[\|x_i^{t,k}-\bar x^{t,k}\|^2\mid\mathcal F_{t\tau}].$$
--   Formalization note: direct source theorem, the conditional estimate of Lemma 1.
--
--   Source: Jianyu Wang et al., A Field Guide to Federated Optimization, arXiv:2107.06917v1, https://arxiv.org/abs/2107.06917v1; Section 6.1.2, PDF p. 41, Lemma 1 (unnumbered display); Appendix D.1, PDF pp. 86–87, equations (24)–(27).
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
--   Jianyu Wang et al., A Field Guide to Federated Optimization, arXiv:2107.06917v1, https://arxiv.org/abs/2107.06917v1; Section 6.1.2, PDF p. 41, Lemma 1 (unnumbered display); Appendix D.1, PDF pp. 86–87, equations (24)–(27).

import Definitions.Def_FedAvg_Model
open MeasureTheory
universe u

namespace FedAvg
theorem PerRoundProgress :
  ∀ (d M : ℕ) (P : Problem d M) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ T : ℕ) (η : ℝ),
    0 < τ → 0 < T → 0 < η → η ≤ 1 / (4 * P.L) →
    ∀ (R : Run P μ τ T η) (t : ℕ), t < T →
      μ[roundLoss R t | R.history (t * τ)] ≤ᵐ[μ] progressRHS R t := by sorry
end FedAvg
