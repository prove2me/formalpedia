-- Prove2me | solution 1 for BanditAlgorithm.gittinsRetirementValue_pos_of_lt_index
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T04:07:42.023478+00:00
-- url     : https://prove2.me/submissions/fd343ff3-9cc6-4879-a91a-302300470056

import Theorems.Thm_BanditAlgorithm_gittins_epsilon_optimal_stopping
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
    (x : S) (γ : ℝ) (hg : γ < gittinsIndex P r α x) :
    0 < gittinsRetirementValue P r α γ x := by
  let B : Set ℝ := insert 0 {v : ℝ |
    ∃ τ : (ℕ → S) → ℕ∞,
      IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      v = ∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
        ∂markovChainMeasure P x}
  let G : ℝ := ∑' t : ℕ, α ^ t
  let U : ℝ := (gittinsIndex P r α x - γ) * G
  have hBdd : BddAbove B := by
    refine ⟨max 0 U, ?_⟩
    intro v hv
    rcases hv with (rfl | ⟨τ, hτ, hτ1, rfl⟩)
    · exact le_max_left _ _
    · rw [integral_discountedStoppedSum_sub_charge
        P hr hα0.le hα1 hint x hτ]
      let den : ℝ :=
        ∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
          ∂markovChainMeasure P x
      let num : ℝ :=
        ∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x
      have hbounds :=
        integral_discountedStoppedSum_one_bounds P hα0.le hα1 x hτ hτ1
      have hden : 0 < den := by
        dsimp [den]
        linarith [hbounds.1]
      have hdenG : den ≤ G := by
        exact hbounds.2
      have hratio : num / den ≤ gittinsIndex P r α x :=
        gittins_stopping_ratio_le_index P hr hα0 hα1 hint x τ hτ hτ1
      have hnum :
          num ≤ gittinsIndex P r α x * den := by
        rwa [div_le_iff₀ hden] at hratio
      have hδ : 0 ≤ gittinsIndex P r α x - γ := sub_nonneg.mpr hg.le
      have hmain : num - γ * den ≤ U := by
        have hm :
            (gittinsIndex P r α x - γ) * den ≤
              (gittinsIndex P r α x - γ) * G :=
          mul_le_mul_of_nonneg_left hdenG hδ
        dsimp [U]
        nlinarith
      exact hmain.trans (le_max_right _ _)
  let ε : ℝ := (gittinsIndex P r α x - γ) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨τ, hτ, hτ1, hratio⟩ :=
    gittins_epsilon_optimal_stopping P hr hα0 hα1 hint x hε
  let den : ℝ :=
    ∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
      ∂markovChainMeasure P x
  let num : ℝ :=
    ∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x
  have hden : 0 < den := by
    have hb :=
      integral_discountedStoppedSum_one_bounds P hα0.le hα1 x hτ hτ1
    dsimp [den]
    linarith [hb.1]
  have hγratio : γ < num / den := by
    dsimp [ε, num, den] at hratio ⊢
    linarith
  have hnet : 0 < num - γ * den := by
    rw [lt_div_iff₀ hden] at hγratio
    linarith
  have hmem : num - γ * den ∈ B := by
    right
    refine ⟨τ, hτ, hτ1, ?_⟩
    rw [integral_discountedStoppedSum_sub_charge
      P hr hα0.le hα1 hint x hτ]
  rw [gittinsRetirementValue]
  change 0 < sSup B
  exact hnet.trans_le (le_csSup hBdd hmem)
