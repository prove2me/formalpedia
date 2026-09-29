-- Prove2me | solution 1 for TropicalSheafSampling.tropical_sheaf_reconstruction_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T03:24:26.101423+00:00
-- url     : https://prove2.me/submissions/64bd1de5-bd5a-4ee9-a1fd-59d59c615a46

import Mathlib
import Definitions.Def_Bridges_TropicalNeuralSheafSampling

open TropicalSheafSampling in
theorem solution {S : Type*} [NormedAddCommGroup S] {O : Type*} [NormedAddCommGroup O]
    (r₁ r₂ : S →+ O) (rayleigh : S → ℝ) (lam κ ε : ℝ)
    (_hκε : ε < κ)
    (hclosed : BandlimitedSubClosed rayleigh lam)
    (hcond : HasConditionRadius r₁ rayleigh lam κ)
    (hpert : SheafPerturbationBound r₁ r₂ rayleigh lam ε)
    (s₁ s₂ : S)
    (hbl₁ : TropicalBandlimited rayleigh lam s₁)
    (hbl₂ : TropicalBandlimited rayleigh lam s₂) :
    (κ - ε) * ‖s₁ - s₂‖ ≤ ‖r₂ s₁ - r₂ s₂‖ + ε * (‖s₁‖ + ‖s₂‖) := by
  -- the condition radius applies to the (bandlimited) difference
  have h1 := hcond (s₁ - s₂) (hclosed s₁ s₂ hbl₁ hbl₂)
  rw [map_sub] at h1
  have e1 := hpert s₁ hbl₁
  have e2 := hpert s₂ hbl₂
  have htri : ‖r₁ s₁ - r₁ s₂‖ ≤ ‖r₂ s₁ - r₂ s₂‖ + ‖r₁ s₁ - r₂ s₁‖ + ‖r₁ s₂ - r₂ s₂‖ := by
    have h : r₁ s₁ - r₁ s₂ = (r₂ s₁ - r₂ s₂) + (r₁ s₁ - r₂ s₁) - (r₁ s₂ - r₂ s₂) := by abel
    rw [h]
    exact (norm_sub_le _ _).trans
      (by linarith [norm_add_le (r₂ s₁ - r₂ s₂) (r₁ s₁ - r₂ s₁)])
  have hd : ‖s₁ - s₂‖ ≤ ‖s₁‖ + ‖s₂‖ := norm_sub_le _ _
  by_cases hε : 0 ≤ ε
  · have h2 := mul_nonneg hε (norm_nonneg (s₁ - s₂))
    nlinarith
  · have hε' : ε < 0 := lt_of_not_ge hε
    -- a negative perturbation bound forces both sections to vanish
    have z1 : ‖s₁‖ ≤ 0 := by
      by_contra hc
      have := mul_neg_of_neg_of_pos hε' (lt_of_not_ge hc)
      linarith [norm_nonneg (r₁ s₁ - r₂ s₁)]
    have z2 : ‖s₂‖ ≤ 0 := by
      by_contra hc
      have := mul_neg_of_neg_of_pos hε' (lt_of_not_ge hc)
      linarith [norm_nonneg (r₁ s₂ - r₂ s₂)]
    have n1 : ‖s₁‖ = 0 := le_antisymm z1 (norm_nonneg _)
    have n2 : ‖s₂‖ = 0 := le_antisymm z2 (norm_nonneg _)
    have nd : ‖s₁ - s₂‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
    rw [nd, n1, n2]
    simp
