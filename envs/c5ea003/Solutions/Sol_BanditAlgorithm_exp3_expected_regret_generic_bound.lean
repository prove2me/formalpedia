-- Prove2me | solution 1 for BanditAlgorithm.exp3_expected_regret_generic_bound
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-07-18T17:16:28.661838+00:00
-- url     : https://prove2.me/submissions/131abf2c-fa99-4add-95cc-be1641894fe7

import Theorems.Thm_BanditAlgorithm_exp3_estimate_unbiased
import Theorems.Thm_BanditAlgorithm_exp3_estimate_advantage_bound

open MeasureTheory ProbabilityTheory

theorem solution
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditAlgorithm.BanditPolicy k) (η : ℝ) (hη : 0 < η)
    (hπ : BanditAlgorithm.IsExp3Policy η π) :
    BanditAlgorithm.adversarialRegret n x π ≤
      Real.log k / η + η * n * k / 2 := by
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  rw [BanditAlgorithm.adversarialRegret]
  rw [sub_le_iff_le_add]
  apply ciSup_le
  intro i
  have hbound :=
    BanditAlgorithm.exp3_estimate_advantage_bound hk n hn x hx π η hη hπ i
  rw [BanditAlgorithm.exp3_estimate_unbiased hk n hn x hx π η hη hπ i] at hbound
  linarith
