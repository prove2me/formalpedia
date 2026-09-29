-- Prove2me | solution 1 for likelihood_ratio_gradient
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-10T03:46:15.375095+00:00
-- url     : https://prove2.me/submissions/d856abf5-ddaa-4578-9dac-8772785da90c

import Theorems.Thm_likelihood_ratio_gradient
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset

/-- Likelihood-ratio / REINFORCE gradient identity. Differentiate the finite sum
term by term, then use `deriv log (p θ' a) = p'(a)/p(θ,a)` and cancel `p(θ,a)`. -/
theorem solution : likelihood_ratio_gradient := by
  intro A _ p f θ hdiff hpos
  -- Turn `fun θ' => ∑ a, g a θ'` into `∑ a, g a` (pointwise function sum) for `deriv_sum`.
  have hfn_eq : (fun θ' => ∑ a : A, p θ' a * f a)
      = ∑ a : A, (fun θ' => p θ' a * f a) := by
    ext x
    exact (Finset.sum_apply x (Finset.univ : Finset A) (fun a θ' => p θ' a * f a)).symm
  -- Each summand is differentiable.
  have hdiff_term : ∀ a ∈ (Finset.univ : Finset A),
      DifferentiableAt ℝ (fun θ' => p θ' a * f a) θ :=
    fun a _ => (hdiff a).mul_const (f a)
  rw [hfn_eq, deriv_sum hdiff_term]
  apply Finset.sum_congr rfl
  intro a _
  -- Goal: deriv (fun θ' => p θ' a * f a) θ = p θ a * f a * deriv (fun θ' => log (p θ' a)) θ
  have hne : p θ a ≠ 0 := ne_of_gt (hpos a)
  have hlog : deriv (fun θ' => Real.log (p θ' a)) θ
      = deriv (fun θ' => p θ' a) θ / p θ a :=
    ((hdiff a).hasDerivAt.log hne).deriv
  rw [hlog, deriv_mul_const (hdiff a) (f a)]
  field_simp
