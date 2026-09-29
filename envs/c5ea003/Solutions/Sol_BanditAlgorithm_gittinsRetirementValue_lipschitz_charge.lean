-- Prove2me | solution 1 for BanditAlgorithm.gittinsRetirementValue_lipschitz_charge
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T04:54:17.094468+00:00
-- url     : https://prove2.me/submissions/9390370c-4e24-40b6-9f1f-056dd1108100

import Theorems.Thm_BanditAlgorithm_gittins_stopping_ratio_le_index
import Theorems.Thm_BanditAlgorithm_integral_discountedStoppedSum_sub_charge
import Theorems.Thm_BanditAlgorithm_integral_discountedStoppedSum_one_bounds
import Definitions.Def_GittinsRetirementValue

open MeasureTheory ProbabilityTheory ENNReal
open BanditAlgorithm

theorem solution
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (γ δ : ℝ) :
    |gittinsRetirementValue P r α γ x -
        gittinsRetirementValue P r α δ x| ≤
      |γ - δ| * ∑' t : ℕ, α ^ t := by
  let G : ℝ := ∑' t : ℕ, α ^ t
  let B : ℝ → Set ℝ := fun c ↦ insert 0 {v : ℝ |
    ∃ τ : (ℕ → S) → ℕ∞,
      IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      v = ∫ ω, discountedStoppedSum α (fun y ↦ r y - c) τ ω
        ∂markovChainMeasure P x}
  have hG0 : 0 ≤ G := tsum_nonneg fun t ↦ pow_nonneg hα0.le t
  have hB0 : ∀ c, (0 : ℝ) ∈ B c := fun c ↦ Set.mem_insert 0 _
  have hBdd : ∀ c, BddAbove (B c) := by
    intro c
    refine ⟨max 0 ((gittinsIndex P r α x - c) * G), ?_⟩
    intro v hv
    rcases hv with (rfl | ⟨τ, hτ, hτ1, rfl⟩)
    · exact le_max_left _ _
    · rw [integral_discountedStoppedSum_sub_charge
        P hr hα0.le hα1 hint x hτ]
      let den : ℝ :=
        ∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
          ∂markovChainMeasure P x
      let num : ℝ :=
        ∫ ω, discountedStoppedSum α r τ ω
          ∂markovChainMeasure P x
      have hbounds :=
        integral_discountedStoppedSum_one_bounds
          P hα0.le hα1 x hτ hτ1
      have hden0 : 0 ≤ den := by
        dsimp [den]
        linarith [hbounds.1]
      have hdenG : den ≤ G := by
        simpa [den, G] using hbounds.2
      have hratio :=
        gittins_stopping_ratio_le_index
          P hr hα0 hα1 hint x τ hτ hτ1
      have hden1 : 1 ≤ den := by
        simpa [den] using hbounds.1
      have hdenpos : 0 < den := by linarith
      have hnum :
          num ≤ gittinsIndex P r α x * den := by
        rw [div_le_iff₀ hdenpos] at hratio
        simpa [num, den] using hratio
      have hnet :
          num - c * den ≤
            max 0 ((gittinsIndex P r α x - c) * G) := by
        by_cases hc : 0 ≤ gittinsIndex P r α x - c
        · have hm :
              (gittinsIndex P r α x - c) * den ≤
                (gittinsIndex P r α x - c) * G :=
            mul_le_mul_of_nonneg_left hdenG hc
          calc
            num - c * den
                ≤ (gittinsIndex P r α x - c) * den := by
                  linarith
            _ ≤ (gittinsIndex P r α x - c) * G := hm
            _ ≤ max 0 ((gittinsIndex P r α x - c) * G) :=
              le_max_right _ _
        · have hc' : gittinsIndex P r α x - c ≤ 0 := le_of_not_ge hc
          have hm :
              (gittinsIndex P r α x - c) * den ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hc' hden0
          calc
            num - c * den
                ≤ (gittinsIndex P r α x - c) * den := by
                  linarith
            _ ≤ 0 := hm
            _ ≤ max 0 ((gittinsIndex P r α x - c) * G) :=
              le_max_left _ _
      simpa [num, den] using hnet
  have hone :
      ∀ c d, sSup (B c) ≤ sSup (B d) + |c - d| * G := by
    intro c d
    apply csSup_le
    · exact ⟨0, hB0 c⟩
    · intro v hv
      have hsup0 : 0 ≤ sSup (B d) :=
        le_csSup (hBdd d) (hB0 d)
      rcases hv with (rfl | ⟨τ, hτ, hτ1, rfl⟩)
      · exact add_nonneg hsup0
          (mul_nonneg (abs_nonneg _) hG0)
      · let den : ℝ :=
          ∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
            ∂markovChainMeasure P x
        let num : ℝ :=
          ∫ ω, discountedStoppedSum α r τ ω
            ∂markovChainMeasure P x
        let w : ℝ := num - d * den
        have hbounds :=
          integral_discountedStoppedSum_one_bounds
            P hα0.le hα1 x hτ hτ1
        have hden0 : 0 ≤ den := by
          dsimp [den]
          linarith [hbounds.1]
        have hdenG : den ≤ G := by
          simpa [den, G] using hbounds.2
        have hwmem : w ∈ B d := by
          right
          refine ⟨τ, hτ, hτ1, ?_⟩
          rw [integral_discountedStoppedSum_sub_charge
            P hr hα0.le hα1 hint x hτ]
        have hw : w ≤ sSup (B d) := le_csSup (hBdd d) hwmem
        have hcd : d - c ≤ |c - d| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        have hmul₁ : (d - c) * den ≤ |c - d| * den :=
          mul_le_mul_of_nonneg_right hcd hden0
        have hmul₂ : |c - d| * den ≤ |c - d| * G :=
          mul_le_mul_of_nonneg_left hdenG (abs_nonneg _)
        rw [integral_discountedStoppedSum_sub_charge
          P hr hα0.le hα1 hint x hτ]
        dsimp [num, den, w] at hw ⊢
        linarith
  rw [gittinsRetirementValue, gittinsRetirementValue]
  change |sSup (B γ) - sSup (B δ)| ≤ |γ - δ| * G
  rw [abs_le]
  constructor
  · have hs := hone δ γ
    rw [abs_sub_comm δ γ] at hs
    linarith
  · linarith [hone γ δ]
