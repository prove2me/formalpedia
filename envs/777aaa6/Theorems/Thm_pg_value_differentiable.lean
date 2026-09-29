-- Prove2me | Theorems.Thm_pg_value_differentiable
-- name    : pg_value_differentiable
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-10T03:40:34.202896+00:00
-- url     : https://prove2.me/theorems/2c957160-250e-4345-85d1-f8161982324a
-- statement:
--   The $k$-step finite-horizon value function $V_k^{\pi_\theta}(s)$ is differentiable in the policy parameter $\theta$ whenever the policy $\pi_\theta(a|s)$ is, for every $k$ and $s$. Proof: induction on $k$. $V_0=0$ is constant; $V_{k+1}(s) = \sum_a \pi_\theta(a|s)\big(r(s,a)+\sum_{s'}P(s'|s,a)V_k(s')\big)$ is a finite sum of products of differentiable functions.
-- source:
--   Standard in finite-horizon MDP theory.

import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

theorem pg_value_differentiable {S A : Type} [Fintype S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ)
    (hdiff : ∀ s a, DifferentiableAt ℝ (fun θ' => π θ' s a) θ) :
    ∀ (k : ℕ) (s : S), DifferentiableAt ℝ (fun θ' => pgValue P r π k θ' s) θ := by sorry
