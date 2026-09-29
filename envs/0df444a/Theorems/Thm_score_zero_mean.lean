-- Prove2me | Theorems.Thm_score_zero_mean
-- name    : score_zero_mean
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-10T04:40:22.993977+00:00
-- url     : https://prove2.me/theorems/e4f0eb43-d3c6-40b8-a09d-435449f3b9f7
-- statement:
--   The score function has zero mean: $$\sum_a p_\theta(a)\,\nabla_\theta\log p_\theta(a) = \mathbb{E}_{a\sim p_\theta}[\nabla_\theta\log p_\theta(a)] = 0.$$ This is the fundamental identity behind baseline-invariance of policy gradient estimators and the Fisher information definition. Proof: $\sum_a p_\theta(a)\frac{p_\theta'(a)}{p_\theta(a)} = \sum_a p_\theta'(a) = \frac{d}{d\theta}\sum_a p_\theta(a) = \frac{d}{d\theta}1 = 0$. Requires $p_{\theta'}$ normalized for all $\theta'$ (not just at $\theta$).
-- source:
--   Classical probability / information geometry.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

theorem score_zero_mean {A : Type} [Fintype A]
    (p : ℝ → A → ℝ) (θ : ℝ)
    (hdiff : ∀ a, DifferentiableAt ℝ (fun θ' => p θ' a) θ)
    (hpos : ∀ a, 0 < p θ a)
    (hnorm : ∀ θ', ∑ a : A, p θ' a = 1) :
    ∑ a : A, p θ a * deriv (fun θ' => Real.log (p θ' a)) θ = 0 := by sorry
