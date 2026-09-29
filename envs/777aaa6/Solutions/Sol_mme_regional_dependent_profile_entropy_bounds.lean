-- Prove2me | solution 1 for mme_regional_dependent_profile_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:52:03.812189+00:00
-- url     : https://prove2.me/submissions/8755209f-3846-4209-b54d-ee8f201926eb

import Theorems.Thm_mme_regional_histogram_entropy_bounds
import Mathlib
open BigOperators MME.RegionRate MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem solution {R : Type*} [Fintype R] {A : R → Type*} [∀ r, Fintype (A r)]
    (mu : ∀ r, A r → ℕ) (S : ℕ) (hS : ∀ r, ∑ a, mu r a ≤ S) :
    (∏ r, ((∑ a, mu r a).factorial / ∏ a, (mu r a).factorial : ℕ) : ℝ) ≤
      Real.exp (∑ r, massEntropy (fun a ↦ (mu r a : ℝ))) ∧
    Real.exp (∑ r, massEntropy (fun a ↦ (mu r a : ℝ))) ≤
      (6 * ((S : ℝ) + 1)) ^ (∑ r, Fintype.card (A r)) *
        (∏ r, ((∑ a, mu r a).factorial / ∏ a, (mu r a).factorial : ℕ) : ℝ) := by
  have hr (r : R) := mme_regional_histogram_entropy_bounds (fun _ : Unit ↦ mu r) S
    (fun _ ↦ hS r)
  simp only [histogramNumber,Fintype.prod_unique,Fintype.sum_unique,Fintype.card_unique,
    one_mul] at hr
  constructor
  · rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun r _ ↦ Nat.cast_nonneg _) (fun r _ ↦ (hr r).1)
  · rw [Real.exp_sum]
    calc
      _ ≤ ∏ r, ((6 * ((S : ℝ) + 1)) ^ Fintype.card (A r) *
          ((∑ a, mu r a).factorial / ∏ a, (mu r a).factorial : ℕ)) :=
        Finset.prod_le_prod (fun r _ ↦ (Real.exp_pos _).le) (fun r _ ↦ (hr r).2)
      _ = _ := by rw [Finset.prod_mul_distrib,← Finset.prod_pow_eq_pow_sum]
