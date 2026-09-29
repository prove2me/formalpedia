-- Prove2me | Theorems.Thm_policy_gradient_baseline
-- name    : policy_gradient_baseline
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-10T04:40:30.787373+00:00
-- url     : https://prove2.me/theorems/6476d4ee-cbe7-42ab-8f02-14b1a1c089fd
-- statement:
--   Baseline-invariance of the policy gradient estimator: for *any* baseline $b_t(s)$ (independent of the action $a$), $$\nabla_\theta V_T(s_0) = \sum_{t<T}\sum_s\rho_t(s)\sum_a\pi_\theta(a|s)\,\big(Q_{T-1-t}(s,a) - b_t(s)\big)\,\nabla_\theta\log\pi_\theta(a|s).$$ This is the REINFORCE-with-baseline identity (Williams 1992). The most common choice $b_t(s) = V_{T-1-t}(s)$ gives the *advantage* form. Follows from `policy_gradient_log_form` and `score_zero_mean` (the $b_t(s)$ term drops out because $\sum_a\pi_\theta(a|s)\nabla\log\pi_\theta(a|s)=0$). Requires the policy normalized for all $\theta'$ near $\theta$, not just at $\theta$.
-- source:
--   R. J. Williams. Simple statistical gradient-following algorithms for connectionist reinforcement learning. ML 8, 1992.

import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

theorem policy_gradient_baseline {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ)
    (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ' => π θ' s a) θ)
    (hpos : ∀ s a, 0 < π θ s a)
    (hnorm : ∀ θ' s, ∑ a : A, π θ' s a = 1)
    (T : ℕ) (s₀ : S) (b : ℕ → S → ℝ) :
    deriv (fun θ' => pgValue P r π T θ' s₀) θ
      = ∑ t ∈ Finset.range T, ∑ s : S, pgRho P π t s₀ θ s
          * ∑ a : A, π θ s a * (pgQ P r π (T - 1 - t) θ s a - b t s)
              * deriv (fun θ' => Real.log (π θ' s a)) θ := by sorry
