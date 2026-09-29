-- Prove2me | Theorems.Thm_pg_bellman_step
-- name    : pg_bellman_step
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-10T03:40:41.529356+00:00
-- url     : https://prove2.me/theorems/7a976fe5-dcb7-4370-85af-b944c8a61cda
-- statement:
--   The one-step (Bellman) gradient identity for the finite-horizon value function. Differentiating the backward recursion $V_{k+1}(s) = \sum_a \pi_\theta(a|s)\,Q_k(s,a)$ by the product rule (and using that $r(s,a)$ and $P(s'|s,a)$ are $\theta$-independent), $$\nabla_\theta V_{k+1}(s) = \sum_a Q_k(s,a)\,\nabla_\theta\pi_\theta(a|s) + \sum_a \pi_\theta(a|s)\sum_{s'}P(s'|s,a)\,\nabla_\theta V_k(s').$$ This is the inductive engine of the policy gradient theorem: a score term plus a discounted expectation of the next-state gradient. Needs `pg_value_differentiable` to rewrite `deriv` of the inner value functions.
-- source:
--   R. Sutton, D. McAllester, S. Singh, Y. Mansour. Policy Gradient Methods for Reinforcement Learning with Function Approximation. NeurIPS 1999.

import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

theorem pg_bellman_step {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ)
    (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ' => π θ' s a) θ)
    (k : ℕ) (s : S) :
    deriv (fun θ' => pgValue P r π (k+1) θ' s) θ
      = (∑ a : A, pgQ P r π k θ s a * deriv (fun θ' => π θ' s a) θ)
        + ∑ a : A, π θ s a * ∑ s' : S, P s a s' * deriv (fun θ' => pgValue P r π k θ' s') θ := by sorry
