-- Prove2me | solution 1 for pg_rho_forward_recursion
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-10T04:32:11.672997+00:00
-- url     : https://prove2.me/submissions/7212c867-8d41-4a72-b87a-a1538b8a25da

import Theorems.Thm_pg_rho_forward_recursion
import Definitions.Def_pg_mdp_core
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open Finset

namespace PGFwd

variable {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
variable (P : S → A → S → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ)

/-- One-step transition weight. -/
noncomputable def W (s s' : S) : ℝ := ∑ a : A, π θ s a * P s a s'

lemma ite_sum_left (s₀ : S) (g : S → ℝ) :
    (∑ s' : S, (if s' = s₀ then (1:ℝ) else 0) * g s') = g s₀ := by
  have : ∀ s' : S, (if s' = s₀ then (1:ℝ) else 0) * g s' = if s' = s₀ then g s' else 0 := by
    intro s'; split <;> simp
  rw [Finset.sum_congr rfl (fun s' _ => this s'), Finset.sum_ite_eq' Finset.univ s₀ g]; simp

lemma ite_sum_right (s₀ : S) (g : S → ℝ) :
    (∑ s' : S, g s' * (if s' = s₀ then (1:ℝ) else 0)) = g s₀ := by
  have : ∀ s' : S, g s' * (if s' = s₀ then (1:ℝ) else 0) = if s' = s₀ then g s' else 0 := by
    intro s'; split <;> simp
  rw [Finset.sum_congr rfl (fun s' _ => this s'), Finset.sum_ite_eq' Finset.univ s₀ g]; simp

end PGFwd

open PGFwd

theorem solution : pg_rho_forward_recursion := by
  intro S A _ _ _ P π θ t
  induction t with
  | zero =>
    intro s₀ s
    -- LHS: ρ_1(s₀,s) = ∑_{s'} W(s₀,s')·[s=s'] = W(s₀,s).
    -- RHS: ∑_{s'} [s'=s₀]·W(s',s) = W(s₀,s).
    calc pgRho P π 1 s₀ θ s
        = ∑ s' : S, W P π θ s₀ s' * (if s = s' then (1:ℝ) else 0) := by
          rw [show pgRho P π 1 s₀ θ s
              = ∑ s' : S, (∑ a : A, π θ s₀ a * P s₀ a s') * pgRho P π 0 s' θ s from rfl]
          apply Finset.sum_congr rfl; intro s' _; rfl
      _ = W P π θ s₀ s := by
          have : ∀ s' : S, W P π θ s₀ s' * (if s = s' then (1:ℝ) else 0)
              = (if s' = s then W P π θ s₀ s' else 0) := by
            intro s'; split <;> rename_i h <;> simp_all [eq_comm]
          rw [Finset.sum_congr rfl (fun s' _ => this s'), Finset.sum_ite_eq' Finset.univ s (W P π θ s₀)]
          simp
      _ = ∑ s' : S, (if s' = s₀ then (1:ℝ) else 0) * W P π θ s' s :=
          (ite_sum_left s₀ (fun s' => W P π θ s' s)).symm
      _ = ∑ s' : S, pgRho P π 0 s₀ θ s' * ∑ a : A, π θ s' a * P s' a s := by
          apply Finset.sum_congr rfl; intro s' _; rfl
  | succ t ih =>
    intro s₀ s
    -- LHS: ρ_{t+2}(s₀,s) = ∑_u W(s₀,u)·ρ_{t+1}(u,s) = ∑_u W(s₀,u)·∑_{s'} ρ_t(u,s')·W(s',s)  [IH]
    --     = ∑_{s'} (∑_u W(s₀,u)·ρ_t(u,s'))·W(s',s) = ∑_{s'} ρ_{t+1}(s₀,s')·W(s',s).
    calc pgRho P π (t + 1 + 1) s₀ θ s
        = ∑ u : S, W P π θ s₀ u * pgRho P π (t + 1) u θ s := by
          rw [show pgRho P π (t + 1 + 1) s₀ θ s
              = ∑ u : S, (∑ a : A, π θ s₀ a * P s₀ a u) * pgRho P π (t + 1) u θ s from rfl]
          rfl
      _ = ∑ u : S, W P π θ s₀ u * ∑ s' : S, pgRho P π t u θ s' * W P π θ s' s := by
          apply Finset.sum_congr rfl; intro u _; congr 1
          rw [ih u s]
          apply Finset.sum_congr rfl; intro s' _; rfl
      _ = ∑ u : S, ∑ s' : S, W P π θ s₀ u * pgRho P π t u θ s' * W P π θ s' s := by
          apply Finset.sum_congr rfl; intro u _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s' _; ring
      _ = ∑ s' : S, ∑ u : S, W P π θ s₀ u * pgRho P π t u θ s' * W P π θ s' s := Finset.sum_comm
      _ = ∑ s' : S, (∑ u : S, W P π θ s₀ u * pgRho P π t u θ s') * W P π θ s' s := by
          apply Finset.sum_congr rfl; intro s' _; rw [Finset.sum_mul]
      _ = ∑ s' : S, pgRho P π (t + 1) s₀ θ s' * ∑ a : A, π θ s' a * P s' a s := rfl
