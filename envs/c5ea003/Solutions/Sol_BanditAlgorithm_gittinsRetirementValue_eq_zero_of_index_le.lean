-- Prove2me | solution 1 for BanditAlgorithm.gittinsRetirementValue_eq_zero_of_index_le
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T04:02:47.156376+00:00
-- url     : https://prove2.me/submissions/b37a4217-f588-4171-bfe5-4a0aa660fee1

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Theorems.Thm_BanditAlgorithm_discountedStoppedSum_sub_charge
import Theorems.Thm_BanditAlgorithm_gittins_stopping_ratio_le_index
import Theorems.Thm_BanditAlgorithm_integrable_discountedStoppedSum
import Theorems.Thm_BanditAlgorithm_integrable_discountedStoppedSum_one
import Definitions.Def_GittinsRetirementValue

open MeasureTheory ProbabilityTheory ENNReal
open BanditAlgorithm

private theorem measurable_abs_tsum
    {S : Type*} [MeasurableSpace S] {α : ℝ} {r : S → ℝ}
    (hr : Measurable r) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) := by
  apply Measurable.tsum
  intro t
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul (by
      have : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
        hr.comp (measurable_pi_apply t)
      fun_prop))

private theorem ae_summable_abs
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    ∀ᵐ ω ∂markovChainMeasure P x,
      Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|) := by
  have hfinite :
      ∀ᵐ ω ∂markovChainMeasure P x,
        (∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) < ⊤ :=
    ae_lt_top (measurable_abs_tsum hr) (ne_of_lt (hint x))
  filter_upwards [hfinite] with ω hω
  have hs := ENNReal.summable_toReal (ne_of_lt hω)
  simpa [ENNReal.toReal_ofReal
    (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs

private theorem stopped_one_ge_one
    {S : Type*} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : (ℕ → S) → ℕ∞} (hτ1 : ∀ ω, 1 ≤ τ ω) (ω : ℕ → S) :
    1 ≤ discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ ω := by
  let f : ℕ → ℝ :=
    fun t ↦ if (t : ℕ∞) < τ ω then α ^ t * (1 : ℝ) else 0
  have hfsum : Summable f := by
    apply Summable.of_norm_bounded
      (summable_geometric_of_norm_lt_one (K := ℝ) (by
        rw [Real.norm_eq_abs, abs_of_nonneg hα0]
        exact hα1))
    intro t
    by_cases ht : (t : ℕ∞) < τ ω
    · simp [f, ht, abs_of_nonneg hα0]
    · simp [f, ht, pow_nonneg hα0 t]
  rw [show discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ ω =
      ∑' t, f t by rfl, hfsum.tsum_eq_zero_add]
  have hzero : (0 : ℕ∞) < τ ω :=
    lt_of_lt_of_le (by norm_num) (hτ1 ω)
  have htail : 0 ≤ ∑' t : ℕ, f (t + 1) :=
    tsum_nonneg fun t ↦ by
      unfold f
      split_ifs <;> positivity
  simpa [f, hzero] using add_le_add_left htail 1

private theorem integral_one_pos
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ)
    (hτ1 : ∀ ω, 1 ≤ τ ω) :
    0 < ∫ ω, discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ ω
      ∂markovChainMeasure P x := by
  letI : IsProbabilityMeasure (markovChainMeasure P x) := by
    rw [markovChainMeasure]
    infer_instance
  have hi := integral_mono (integrable_const (1 : ℝ))
    (integrable_discountedStoppedSum_one P hα0 hα1 x hτ)
    (stopped_one_ge_one hα0 hα1 hτ1)
  have : (1 : ℝ) ≤
      ∫ ω, discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ ω
        ∂markovChainMeasure P x := by simpa using hi
  linarith

private theorem integral_net_eq
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α γ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    (∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
        ∂markovChainMeasure P x) =
      (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x) -
        γ * (∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
          ∂markovChainMeasure P x) := by
  have hae : ∀ᵐ ω ∂markovChainMeasure P x,
      discountedStoppedSum α (fun y ↦ r y - γ) τ ω =
        discountedStoppedSum α r τ ω -
          γ * discountedStoppedSum α (fun _ : S ↦ 1) τ ω := by
    filter_upwards [ae_summable_abs P hr hα0 hint x] with ω hω
    exact discountedStoppedSum_sub_charge hα0 hα1 r τ ω hω
  rw [integral_congr_ae hae]
  rw [integral_sub
    (integrable_discountedStoppedSum P hr hα0 hint x hτ)
    ((integrable_discountedStoppedSum_one P hα0 hα1 x hτ).const_mul γ)]
  rw [integral_const_mul]

theorem solution
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (γ : ℝ) (hg : gittinsIndex P r α x ≤ γ) :
    gittinsRetirementValue P r α γ x = 0 := by
  let B : Set ℝ := insert 0 {v : ℝ |
    ∃ τ : (ℕ → S) → ℕ∞,
      IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      v = ∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
        ∂markovChainMeasure P x}
  have hB0 : (0 : ℝ) ∈ B := Set.mem_insert 0 _
  have hupper : ∀ v ∈ B, v ≤ 0 := by
    intro v hv
    rcases hv with (rfl | ⟨τ, hτ, hτ1, rfl⟩)
    · exact le_rfl
    · rw [integral_net_eq P hr hα0.le hα1 hint x hτ]
      let den : ℝ :=
        ∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
          ∂markovChainMeasure P x
      let num : ℝ :=
        ∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x
      have hden : 0 < den :=
        integral_one_pos P hα0.le hα1 x hτ hτ1
      have hratio : num / den ≤ gittinsIndex P r α x :=
        gittins_stopping_ratio_le_index P hr hα0 hα1 hint x τ hτ hτ1
      have : num ≤ γ * den := by
        rw [div_le_iff₀ hden] at hratio
        nlinarith
      dsimp [num, den] at this ⊢
      linarith
  have hBdd : BddAbove B := ⟨0, hupper⟩
  rw [gittinsRetirementValue]
  change sSup B = 0
  apply le_antisymm
  · exact csSup_le ⟨0, hB0⟩ hupper
  · exact le_csSup hBdd hB0
