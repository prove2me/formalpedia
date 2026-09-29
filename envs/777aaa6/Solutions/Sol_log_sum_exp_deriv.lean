-- Prove2me | solution 1 for log_sum_exp_deriv
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-10T05:22:45.175581+00:00
-- url     : https://prove2.me/submissions/eabc2344-3294-4aeb-bfd4-c01866af0ba8

import Theorems.Thm_log_sum_exp_deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

open Finset Real

/-- The gradient of the log-partition function is the mean of the sufficient statistic. -/
theorem solution : log_sum_exp_deriv := by
  intro A _ _ φ θ
  -- The derivative of each summand exp(θ' φ a) is exp(θ φ a) · φ a.
  have hexp : ∀ a : A, HasDerivAt (fun θ' => Real.exp (θ' * φ a)) (Real.exp (θ * φ a) * φ a) θ := by
    intro a
    have h1 : HasDerivAt (fun θ' : ℝ => θ' * φ a) (φ a) θ := by
      simpa using (hasDerivAt_id θ).mul_const (φ a)
    exact h1.exp
  -- The sum of exps is differentiable with the right derivative.
  have hsum : HasDerivAt (fun θ' => ∑ a : A, Real.exp (θ' * φ a))
      (∑ a : A, Real.exp (θ * φ a) * φ a) θ := HasDerivAt.fun_sum (fun a _ => hexp a)
  -- The sum is positive (hence nonzero), so HasDerivAt.log applies.
  have hpos : (0 : ℝ) < ∑ a : A, Real.exp (θ * φ a) := by
    apply Finset.sum_pos
    · intro a _; exact Real.exp_pos _
    · exact Finset.univ_nonempty
  have hne : (∑ a : A, Real.exp (θ * φ a)) ≠ 0 := ne_of_gt hpos
  exact (hsum.log hne).deriv
