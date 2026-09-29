-- Prove2me | solution 1 for policy_gradient_baseline
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-10T04:45:45.119062+00:00
-- url     : https://prove2.me/submissions/2eca5cf7-3494-43e8-8ab4-b15b710d25d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_policy_gradient_baseline
import Theorems.Thm_policy_gradient_log_form
import Theorems.Thm_score_zero_mean
import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

open Finset

/-- Baseline invariance of the policy gradient: the baseline `b t s` contributes
`b t s · ∑_a π ∇log π = b t s · 0 = 0`, so it can be subtracted freely. -/
theorem solution : policy_gradient_baseline := by
  intro S A _ _ _ P r π θ hdiff hpos hnorm T s₀ b
  rw [policy_gradient_log_form P r π θ hdiff hpos T s₀]
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro s _
  congr 1
  have hzero : (∑ a : A, π θ s a * deriv (fun θ' => Real.log (π θ' s a)) θ) = 0 :=
    score_zero_mean (fun θ' a => π θ' s a) θ (fun a => hdiff s a) (fun a => hpos s a)
      (fun θ' => hnorm θ' s)
  calc (∑ a : A, π θ s a * pgQ P r π (T - 1 - t) θ s a * deriv (fun θ' => Real.log (π θ' s a)) θ)
      = (∑ a : A, π θ s a * (pgQ P r π (T - 1 - t) θ s a - b t s)
          * deriv (fun θ' => Real.log (π θ' s a)) θ)
        + b t s * (∑ a : A, π θ s a * deriv (fun θ' => Real.log (π θ' s a)) θ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro a _; ring
    _ = (∑ a : A, π θ s a * (pgQ P r π (T - 1 - t) θ s a - b t s)
          * deriv (fun θ' => Real.log (π θ' s a)) θ) + b t s * 0 := by rw [hzero]
    _ = ∑ a : A, π θ s a * (pgQ P r π (T - 1 - t) θ s a - b t s)
          * deriv (fun θ' => Real.log (π θ' s a)) θ := by ring
