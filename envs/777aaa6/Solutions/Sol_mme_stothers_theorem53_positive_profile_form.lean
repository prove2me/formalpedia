-- Prove2me | solution 1 for mme_stothers_theorem53_positive_profile_form
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-21T23:35:47.85265+00:00
-- url     : https://prove2.me/submissions/b4b5133a-e62c-4b6b-abbd-1458cdd771a0

import Theorems.Thm_mme_stothers_positive_stationary_profile_exists_unique
import Theorems.Thm_mme_stothers_theorem53_slice_stationary_form
import Mathlib.Tactic.LinearCombination

open MME
universe u
set_option autoImplicit false

/-- The stationary profile in Theorem 5.3 exists for every positive admissible profile. -/
theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (a : Fin 10 → ℝ) (ha : MME.StothersFourth.InZ a)
    (hapos : ∀ i, 0 < a i) :
    ∃ b : Fin 10 → ℝ, MME.StothersFourth.InN b ∧ (∀ i, 0 < b i) ∧
      MME.StothersFourth.InY (fun i ↦ a i - b i) ∧
      ∀ V : ℝ, 0 ≤ V →
        V < MME.StothersFourth.globalRate 6 tau a a *
          (MME.StothersFourth.entropyProduct b / MME.StothersFourth.entropyProduct a) →
        HasTauValueAtLeast (MME.StothersFourth.cwFourthObj K 6) tau V := by
  obtain ⟨b, ⟨hbN, hbpos, hba⟩, _⟩ :=
    mme_stothers_positive_stationary_profile_exists_unique a ha hapos
  have hab : MME.StothersFourth.InY (fun i ↦ a i - b i) := by
    obtain ⟨s, t, hst⟩ := hba
    refine ⟨-s, -t, fun i ↦ ?_⟩
    linear_combination -hst i
  exact ⟨b, hbN, hbpos, hab,
    mme_stothers_theorem53_slice_stationary_form tau htauLower htauUpper a b ha hbN
      hapos hbpos hab⟩
