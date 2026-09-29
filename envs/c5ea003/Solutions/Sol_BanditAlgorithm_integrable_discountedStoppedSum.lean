-- Prove2me | solution 1 for BanditAlgorithm.integrable_discountedStoppedSum
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T04:01:48.892278+00:00
-- url     : https://prove2.me/submissions/01209740-4d78-47b4-af35-d4d21492bc50

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory ENNReal
open BanditAlgorithm

private theorem trajectoryFiltration_le' {S : Type*} [MeasurableSpace S] (n : ℕ) :
    trajectoryFiltration S n ≤ (inferInstance : MeasurableSpace (ℕ → S)) := by
  intro s hs
  rcases hs with ⟨u, hu, rfl⟩
  exact hu.preimage (by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply i.1)

private theorem measurableSet_lt_trajStoppingTime'
    {S : Type*} [MeasurableSpace S] {τ : (ℕ → S) → ℕ∞}
    (hτ : IsTrajStoppingTime τ) (t : ℕ) :
    MeasurableSet {ω | (t : ℕ∞) < τ ω} := by
  rw [show {ω | (t : ℕ∞) < τ ω} = {ω | τ ω ≤ (t : ℕ∞)}ᶜ by
    ext ω
    simp]
  exact ((trajectoryFiltration_le' t) _ (hτ t)).compl

private theorem measurable_discountedStoppedSum'
    {S : Type*} [MeasurableSpace S] {α : ℝ} {f : S → ℝ}
    (hf : Measurable f) {τ : (ℕ → S) → ℕ∞}
    (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum α f τ) := by
  unfold discountedStoppedSum
  apply Measurable.tsum
  intro t
  exact Measurable.ite (measurableSet_lt_trajStoppingTime' hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t)))
    measurable_const

private theorem measurable_discountedAbsSeries'
    {S : Type*} [MeasurableSpace S] {α : ℝ} (hα0 : 0 ≤ α)
    {r : S → ℝ} (hr : Measurable r) :
    Measurable (fun ω : ℕ → S ↦ ∑' t : ℕ, α ^ t * |r (ω t)|) := by
  apply Measurable.tsum
  intro t
  have ht : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
    hr.comp (measurable_pi_apply t)
  exact measurable_const.mul (by fun_prop)

private theorem measurable_discountedAbsSeriesENNReal'
    {S : Type*} [MeasurableSpace S] {α : ℝ} (hα0 : 0 ≤ α)
    {r : S → ℝ} (hr : Measurable r) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) := by
  apply Measurable.ennreal_tsum
  intro t
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul (by
      have ht : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
        hr.comp (measurable_pi_apply t)
      fun_prop))

private theorem ae_summable_discountedAbsSeries'
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    ∀ᵐ ω ∂markovChainMeasure P x,
      Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|) := by
  have hfinite :
      ∀ᵐ ω ∂markovChainMeasure P x,
        (∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) < ⊤ :=
    ae_lt_top (measurable_discountedAbsSeriesENNReal' hα0 hr)
      (ne_of_lt (hint x))
  filter_upwards [hfinite] with ω hω
  have hs := ENNReal.summable_toReal (ne_of_lt hω)
  simpa [ENNReal.toReal_ofReal
    (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs

private theorem integrable_discountedAbsSeries'
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    Integrable (fun ω : ℕ → S ↦ ∑' t : ℕ, α ^ t * |r (ω t)|)
      (markovChainMeasure P x) := by
  refine ⟨(measurable_discountedAbsSeries' hα0 hr).aestronglyMeasurable, ?_⟩
  have hnonneg :
      ∀ᵐ ω ∂markovChainMeasure P x,
        0 ≤ ∑' t : ℕ, α ^ t * |r (ω t)| :=
    Filter.Eventually.of_forall fun ω ↦ tsum_nonneg fun t ↦
      mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
  rw [hasFiniteIntegral_iff_ofReal hnonneg]
  calc
    (∫⁻ ω, ENNReal.ofReal (∑' t : ℕ, α ^ t * |r (ω t)|)
        ∂markovChainMeasure P x) =
        ∫⁻ ω, ∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)
          ∂markovChainMeasure P x := by
      apply lintegral_congr_ae
      filter_upwards [ae_summable_discountedAbsSeries' P hr hα0 hint x]
        with ω hω
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦ mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω
    _ < ⊤ := hint x

theorem solution
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    Integrable (discountedStoppedSum α r τ) (markovChainMeasure P x) := by
  apply (integrable_discountedAbsSeries' P hr hα0 hint x).mono
    (measurable_discountedStoppedSum' hr hτ).aestronglyMeasurable
  filter_upwards [ae_summable_discountedAbsSeries' P hr hα0 hint x]
    with ω hω
  let f : ℕ → ℝ :=
    fun t ↦ if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0
  have hnorm : ∀ t, ‖f t‖ ≤ α ^ t * |r (ω t)| := by
    intro t
    by_cases ht : (t : ℕ∞) < τ ω
    · simp [f, ht, abs_of_nonneg hα0]
    · simp [f, ht, mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)]
  have hfsum : Summable f := Summable.of_norm_bounded hω hnorm
  calc
    ‖discountedStoppedSum α r τ ω‖ = ‖∑' t, f t‖ := rfl
    _ ≤ ∑' t, ‖f t‖ := norm_tsum_le_tsum_norm hfsum.norm
    _ ≤ ∑' t, α ^ t * |r (ω t)| :=
      hfsum.norm.tsum_le_tsum hnorm hω
    _ = ‖∑' t, α ^ t * |r (ω t)|‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
