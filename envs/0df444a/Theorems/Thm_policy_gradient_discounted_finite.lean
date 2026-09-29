-- Prove2me | Theorems.Thm_policy_gradient_discounted_finite
-- name    : policy_gradient_discounted_finite
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-10T05:05:28.937217+00:00
-- url     : https://prove2.me/theorems/17f5fe86-aab4-4d16-bdf9-14cf60239e84
-- statement:
--   The discounted finite-horizon policy gradient theorem (the form actually used in practice): $$\nabla_\theta V_T^{\gamma,\pi_\theta}(s_0) = \sum_{t=0}^{T-1}\gamma^t\sum_s\rho_t(s\mid s_0)\sum_a Q_{T-1-t}^{\gamma}(s,a)\,\nabla_\theta\pi_\theta(a\mid s).$$ The discounted $T$-step value is `pgValue (γ·P) r π T θ s` (substituting $P\leftarrow\gamma P$ gives exactly the discounted Bellman recursion $V^{\gamma}_{k+1}(s) = \sum_a\pi(a|s)(r(s,a)+\gamma\sum_{s'}P(s'|s,a)V^{\gamma}_k(s'))$), and `pg_rho_gamma_scale` converts `pgRho (γ·P)` to `γ^t · pgRho P`. Thus this follows directly from `policy_gradient_finite_horizon` and `pg_rho_gamma_scale` — no new induction. Taking $T\to\infty$ with $\gamma<1$ gives the classical Sutton et al. 1999 infinite-horizon statement.
-- source:
--   R. Sutton, D. McAllester, S. Singh, Y. Mansour. Policy Gradient Methods for RL with Function Approximation. NeurIPS 1999.

import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

theorem policy_gradient_discounted_finite {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ) (γ : ℝ)
    (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ' => π θ' s a) θ)
    (T : ℕ) (s₀ : S) :
    deriv (fun θ' => pgValue (fun s a s' => γ * P s a s') r π T θ' s₀) θ
      = ∑ t ∈ Finset.range T, γ ^ t * ∑ s : S, pgRho P π t s₀ θ s
          * ∑ a : A, pgQ (fun s a s' => γ * P s a s') r π (T - 1 - t) θ s a
              * deriv (fun θ' => π θ' s a) θ := by sorry
