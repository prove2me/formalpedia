-- Prove2me | Theorems.Thm_FedAvg_BoundedClientDrift
-- name    : FedAvg.BoundedClientDrift
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-22T23:53:09.862735+00:00
-- url     : https://prove2.me/theorems/8bd77bfa-68b9-40f2-a8e3-1e912e6e45a9
-- title:
--   Lemma 2 — Bounded Client Drift
-- statement:
--   ### Mathematical statement
--   For $\tau,T\ge1$, $0<\eta\le1/(4L)$, every $0\le t<T$,
--   every client $i$, and $0\le k\le\tau$,
--   $$\mathbb E[\|x_i^{t,k}-\bar x^{t,k}\|^2\mid\mathcal F_{t\tau}]
--   \le18\tau^2\eta^2\zeta^2+4\tau\eta^2\sigma^2.$$
--   Formalization note: direct source theorem, including the terminal local state;
--   the proof in Appendix D.2 bounds the drift uniformly throughout the round.
--
--   Source: Jianyu Wang et al., A Field Guide to Federated Optimization, arXiv:2107.06917v1, https://arxiv.org/abs/2107.06917v1; Section 6.1.2, PDF p. 41, Lemma 2 (unnumbered display); Appendix D.2, PDF pp. 87–88.
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
--   Jianyu Wang et al., A Field Guide to Federated Optimization, arXiv:2107.06917v1, https://arxiv.org/abs/2107.06917v1; Section 6.1.2, PDF p. 41, Lemma 2 (unnumbered display); Appendix D.2, PDF pp. 87–88.

import Definitions.Def_FedAvg_Model
open MeasureTheory
universe u

namespace FedAvg
theorem BoundedClientDrift :
  ∀ (d M : ℕ) (P : Problem d M) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ T : ℕ) (η : ℝ),
    0 < τ → 0 < T → 0 < η → η ≤ 1 / (4 * P.L) →
    ∀ (R : Run P μ τ T η) (t : ℕ), t < T → ∀ k, k ≤ τ → ∀ i,
      μ[clientDriftSq R t k i | R.history (t * τ)] ≤ᵐ[μ] fun _ ↦ driftRHS P τ η := by sorry
end FedAvg
