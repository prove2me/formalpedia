-- Prove2me | Theorems.Thm_policy_gradient_finite_horizon
-- name    : policy_gradient_finite_horizon
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-10T03:40:49.583268+00:00
-- url     : https://prove2.me/theorems/e5b568fe-d78d-4028-b4d2-650596bcac1f
-- statement:
--   The finite-horizon policy gradient theorem (Sutton, McAllester, Singh, Mansour 1999; finite-horizon, finite-state/action, scalar-parameter form). For a finite MDP with transition kernel $P$, reward $r$, policy $\pi_\theta$ differentiable in a scalar parameter $\theta$, start state $s_0$, and horizon $T$: $$\nabla_\theta V_T^{\pi_\theta}(s_0) = \sum_{t=0}^{T-1}\sum_s \rho_t^{\pi_\theta}(s\,|\,s_0)\sum_a Q_{T-1-t}^{\pi_\theta}(s,a)\,\nabla_\theta\pi_\theta(a|s),$$ where $\rho_t$ is the time-$t$ state visitation probability and $Q_k$ the $k$-steps-remaining action value. Proof: induction on $T$, unrolling `pg_bellman_step`; the inner $\sum_a\pi\sum_{s'}P\cdot\nabla V_k$ term becomes the $t\geq1$ slice of the sum via the first-step recursion for $\rho$. Note no probability axioms on $P,\pi$ are needed for the identity itself; they make $\rho$ and $V$ probabilistically meaningful but the algebra holds regardless.
-- source:
--   R. Sutton, D. McAllester, S. Singh, Y. Mansour. Policy Gradient Methods for Reinforcement Learning with Function Approximation. NeurIPS 1999.

import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

theorem policy_gradient_finite_horizon {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ)
    (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ' => π θ' s a) θ)
    (T : ℕ) (s₀ : S) :
    deriv (fun θ' => pgValue P r π T θ' s₀) θ
      = ∑ t ∈ Finset.range T, ∑ s : S, pgRho P π t s₀ θ s
          * ∑ a : A, pgQ P r π (T - 1 - t) θ s a * deriv (fun θ' => π θ' s a) θ := by sorry
