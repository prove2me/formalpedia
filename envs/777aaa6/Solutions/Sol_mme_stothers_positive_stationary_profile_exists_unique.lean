-- Prove2me | solution 1 for mme_stothers_positive_stationary_profile_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-21T23:33:27.079865+00:00
-- url     : https://prove2.me/submissions/8aecdb53-589d-483d-bd3f-957cb6b48d30

import Theorems.Thm_mme_stothers_slice_entropy_minimum_exists_unique
import Theorems.Thm_mme_stothers_slice_entropy_minimum_support
import Theorems.Thm_mme_stothers_positive_slice_minimum_is_stationary
import Theorems.Thm_mme_stothers_positive_stationary_profile_unique
import Mathlib.Tactic.LinearCombination

open MME.StothersFourth
set_option autoImplicit false

/-- Every slice containing a positive profile has exactly one positive stationary profile. -/
theorem solution
    (a : Fin 10 → ℝ) (ha : InZ a) (hapos : ∀ i, 0 < a i) :
    ∃! b : Fin 10 → ℝ, InN b ∧ (∀ i, 0 < b i) ∧ InY (fun i ↦ b i - a i) := by
  obtain ⟨b, ⟨hb, hba, hmin⟩, _⟩ := mme_stothers_slice_entropy_minimum_exists_unique a ha
  have hbpos : ∀ i, 0 < b i := fun i ↦
    mme_stothers_slice_entropy_minimum_support a b ha hb hba hmin i (hapos i)
  have hbmin : ∀ c : Fin 10 → ℝ, InZ c → InY (fun i ↦ c i - b i) →
      entropyProduct b ≤ entropyProduct c := by
    intro c hc hcb
    apply hmin c hc
    obtain ⟨s, t, hst⟩ := hcb
    obtain ⟨u, v, huv⟩ := hba
    refine ⟨s + u, t + v, fun i ↦ ?_⟩
    linear_combination hst i + huv i
  have hbN := mme_stothers_positive_slice_minimum_is_stationary b hb hbpos hbmin
  refine ⟨b, ⟨hbN, hbpos, hba⟩, ?_⟩
  rintro c ⟨hcN, hcpos, hca⟩
  apply mme_stothers_positive_stationary_profile_unique c b hcN hbN hcpos hbpos
  obtain ⟨s, t, hst⟩ := hca
  obtain ⟨u, v, huv⟩ := hba
  refine ⟨s - u, t - v, fun i ↦ ?_⟩
  linear_combination hst i - huv i
