-- Prove2me | Theorems.Thm_policy_gradient_log_form
-- name    : policy_gradient_log_form
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-10T04:25:49.086242+00:00
-- url     : https://prove2.me/theorems/438be27a-48d9-4bae-927f-6961ab7f725c
-- statement:
--   The log-derivative (score-function / REINFORCE) form of the finite-horizon policy gradient theorem: $$\nabla_\theta V_T^{\pi_\theta}(s_0) = \sum_{t=0}^{T-1}\sum_s \rho_t(s\,|\,s_0)\sum_a \pi_\theta(a|s)\,Q_{T-1-t}(s,a)\,\nabla_\theta\log\pi_\theta(a|s) = \mathbb{E}\Big[\sum_{t<T} Q_{T-1-t}(S_t,A_t)\,\nabla_\theta\log\pi_\theta(A_t|S_t)\Big].$$ This is the form actually implemented by REINFORCE / vanilla policy gradient. Follows from `policy_gradient_finite_horizon` by rewriting $\nabla\pi = \pi\,\nabla\log\pi$ at each $(s,a)$ (requires $\pi_\theta(a|s) > 0$).
-- source:
--   R. J. Williams. Simple statistical gradient-following algorithms for connectionist reinforcement learning. ML 8, 1992 (REINFORCE); Sutton et al. NeurIPS 1999.

import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

theorem policy_gradient_log_form {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ)
    (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ' => π θ' s a) θ)
    (hpos : ∀ s a, 0 < π θ s a)
    (T : ℕ) (s₀ : S) :
    deriv (fun θ' => pgValue P r π T θ' s₀) θ
      = ∑ t ∈ Finset.range T, ∑ s : S, pgRho P π t s₀ θ s
          * ∑ a : A, π θ s a * pgQ P r π (T - 1 - t) θ s a
              * deriv (fun θ' => Real.log (π θ' s a)) θ := by sorry
