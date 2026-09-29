-- Prove2me | Theorems.Thm_log_sum_exp_deriv
-- name    : log_sum_exp_deriv
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-10T05:21:29.573856+00:00
-- url     : https://prove2.me/theorems/093d0f75-ba02-447f-a99b-81037da5207b
-- statement:
--   The gradient of the log-partition (log-sum-exp) function of a 1-parameter exponential family is the mean of the sufficient statistic under the Gibbs distribution: $$\frac{d}{d\theta}\log\sum_a e^{\theta\varphi(a)} = \frac{\sum_a e^{\theta\varphi(a)}\varphi(a)}{\sum_a e^{\theta\varphi(a)}} = \mathbb{E}_{a\sim\text{softmax}(\theta\varphi)}[\varphi(a)].$$ Standard identity in exponential family / information geometry / variational inference. Combined with `policy_gradient_log_form` (on Prove2me), this gives the softmax policy gradient: for $\pi_\theta(a|s) = \mathrm{softmax}(\theta\varphi(s,\cdot))(a)$, $\nabla_\theta\log\pi_\theta(a|s) = \varphi(s,a) - \mathbb{E}_{a'\sim\pi_\theta}[\varphi(s,a')]$. Proof: chain rule on `Real.log` (`HasDerivAt.log`) and `HasDerivAt.fun_sum` / `HasDerivAt.exp`; the denominator is positive since each `exp` is.
-- source:
--   Exponential family / softmax gradient — classical (e.g. Wainwright & Jordan, Graphical Models, Exponential Families, and Variational Inference, 2008, §3).

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

theorem log_sum_exp_deriv {A : Type} [Fintype A] [Nonempty A] (φ : A → ℝ) (θ : ℝ) :
    deriv (fun θ' => Real.log (∑ a : A, Real.exp (θ' * φ a))) θ
      = (∑ a : A, Real.exp (θ * φ a) * φ a) / (∑ a : A, Real.exp (θ * φ a)) := by sorry
