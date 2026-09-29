-- Prove2me | solution 1 for pg_rho_gamma_scale
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-10T05:06:15.361103+00:00
-- url     : https://prove2.me/submissions/33a12ee4-de94-469d-bf7f-959fbc24c48f

import Theorems.Thm_pg_rho_gamma_scale
import Definitions.Def_pg_mdp_core
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open Finset

/-- Discounting the transition kernel scales `pgRho` by `γ^t`. -/
theorem solution : pg_rho_gamma_scale := by
  intro S A _ _ _ P π θ γ t
  induction t with
  | zero =>
    intro s₀ s
    rw [show pgRho (fun s a s' => γ * P s a s') π 0 s₀ θ s = if s = s₀ then (1:ℝ) else 0 from rfl,
        show pgRho P π 0 s₀ θ s = if s = s₀ then (1:ℝ) else 0 from rfl, pow_zero, one_mul]
  | succ m ih =>
    intro s₀ s
    calc pgRho (fun s a s' => γ * P s a s') π (m + 1) s₀ θ s
        = ∑ s' : S, (∑ a : A, π θ s₀ a * (γ * P s₀ a s'))
            * pgRho (fun s a s' => γ * P s a s') π m s' θ s := rfl
      _ = ∑ s' : S, (γ * ∑ a : A, π θ s₀ a * P s₀ a s')
            * (γ ^ m * pgRho P π m s' θ s) := by
          apply Finset.sum_congr rfl; intro s' _
          congr 1
          · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
          · exact ih s' s
      _ = γ ^ (m + 1) * ∑ s' : S, (∑ a : A, π θ s₀ a * P s₀ a s') * pgRho P π m s' θ s := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro s' _; ring
      _ = γ ^ (m + 1) * pgRho P π (m + 1) s₀ θ s := by
          congr 1
