-- Prove2me | solution 1 for policy_gradient_discounted_finite
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-10T05:07:45.986658+00:00
-- url     : https://prove2.me/submissions/bd532a5f-6fdf-4c79-ae99-50f2589d93de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_policy_gradient_discounted_finite
import Theorems.Thm_policy_gradient_finite_horizon
import Theorems.Thm_pg_rho_gamma_scale
import Definitions.Def_pg_mdp_core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open Finset

/-- Discounted finite-horizon PGT: specialize `policy_gradient_finite_horizon` to
`P ← γ·P` and use `pg_rho_gamma_scale`. -/
theorem solution : policy_gradient_discounted_finite := by
  intro S A _ _ _ P r π θ γ hdiff T s₀
  rw [policy_gradient_finite_horizon (fun s a s' => γ * P s a s') r π θ hdiff T s₀]
  apply Finset.sum_congr rfl; intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  rw [pg_rho_gamma_scale P π θ γ t s₀ s]
  ring
