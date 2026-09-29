-- Prove2me | Theorems.Thm_likelihood_ratio_gradient
-- name    : likelihood_ratio_gradient
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-10T03:40:24.024777+00:00
-- url     : https://prove2.me/theorems/78ff276a-b5dc-403e-bb39-bb5c1fc5efe0
-- statement:
--   The likelihood-ratio / REINFORCE gradient identity. For a finite family of strictly positive differentiable weights $p_\theta : A \to \mathbb{R}$, $$\frac{d}{d\theta}\sum_a p_\theta(a)\,f(a) = \sum_a p_\theta(a)\,f(a)\,\frac{d}{d\theta}\log p_\theta(a).$$ This is the score-function trick at the heart of policy-gradient / REINFORCE estimators. Note the normalization $\sum_a p_\theta(a)=1$ is not needed for this pointwise identity. Proof: differentiate the finite sum term by term; $\frac{d}{d\theta}\log p_\theta(a) = p_\theta'(a)/p_\theta(a)$ and the $p_\theta(a)$ cancels.
-- source:
--   R. J. Williams. Simple statistical gradient-following algorithms for connectionist reinforcement learning. Machine Learning 8, 1992 (REINFORCE).

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

theorem likelihood_ratio_gradient {A : Type} [Fintype A]
    (p : ℝ → A → ℝ) (f : A → ℝ) (θ : ℝ)
    (hdiff : ∀ a, DifferentiableAt ℝ (fun θ' => p θ' a) θ)
    (hpos : ∀ a, 0 < p θ a) :
    deriv (fun θ' => ∑ a : A, p θ' a * f a) θ
      = ∑ a : A, p θ a * f a * deriv (fun θ' => Real.log (p θ' a)) θ := by sorry
