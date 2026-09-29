-- Prove2me | solution 1 for BanditAlgorithm.gittins_stopping_ratio_le_index
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T02:56:33.727055+00:00
-- url     : https://prove2.me/submissions/6de9d077-810f-4b5d-a536-66932f15bc1c

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

private theorem trajectoryFiltration_le {S : Type*} [MeasurableSpace S] (n : ℕ) :
    trajectoryFiltration S n ≤ (inferInstance : MeasurableSpace (ℕ → S)) := by
  intro s hs
  rcases hs with ⟨u, hu, rfl⟩
  exact hu.preimage (by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply i.1)

private theorem measurableSet_lt_trajStoppingTime
    {S : Type*} [MeasurableSpace S] {τ : (ℕ → S) → ℕ∞}
    (hτ : IsTrajStoppingTime τ) (t : ℕ) :
    MeasurableSet {ω | (t : ℕ∞) < τ ω} := by
  rw [show {ω | (t : ℕ∞) < τ ω} = {ω | τ ω ≤ (t : ℕ∞)}ᶜ by
    ext ω
    simp]
  exact ((trajectoryFiltration_le t) _ (hτ t)).compl

private theorem measurable_discountedStoppedSum
    {S : Type*} [MeasurableSpace S] {α : ℝ} {f : S → ℝ}
    (hf : Measurable f) {τ : (ℕ → S) → ℕ∞}
    (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum α f τ) := by
  unfold discountedStoppedSum
  apply Measurable.tsum
  intro t
  exact Measurable.ite (measurableSet_lt_trajStoppingTime hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t)))
    measurable_const

private theorem measurable_discountedAbsSeries
    {S : Type*} [MeasurableSpace S] {α : ℝ} (hα0 : 0 ≤ α)
    {r : S → ℝ} (hr : Measurable r) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, α ^ t * |r (ω t)|) := by
  apply Measurable.tsum
  intro t
  have ht : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
    hr.comp (measurable_pi_apply t)
  have habs : Measurable (fun ω : ℕ → S ↦ |r (ω t)|) := by
    fun_prop
  exact measurable_const.mul habs

private theorem measurable_discountedAbsSeriesENNReal
    {S : Type*} [MeasurableSpace S] {α : ℝ} (hα0 : 0 ≤ α)
    {r : S → ℝ} (hr : Measurable r) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) := by
  apply Measurable.ennreal_tsum
  intro t
  have ht : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
    hr.comp (measurable_pi_apply t)
  have habs : Measurable (fun ω : ℕ → S ↦ |r (ω t)|) := by
    fun_prop
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul habs)

private theorem ae_summable_discountedAbsSeries
    {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    ∀ᵐ ω ∂markovChainMeasure P x,
      Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|) := by
  have hfinite :
      ∀ᵐ ω ∂markovChainMeasure P x,
        (∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) < ⊤ :=
    ae_lt_top (measurable_discountedAbsSeriesENNReal hα0 hr)
      (ne_of_lt (hint x))
  filter_upwards [hfinite] with ω hω
  have hs := ENNReal.summable_toReal (ne_of_lt hω)
  simpa [ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))]
    using hs

private theorem integrable_discountedAbsSeries
    {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    Integrable (fun ω : ℕ → S ↦
      ∑' t : ℕ, α ^ t * |r (ω t)|) (markovChainMeasure P x) := by
  refine ⟨(measurable_discountedAbsSeries hα0 hr).aestronglyMeasurable, ?_⟩
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
      filter_upwards [ae_summable_discountedAbsSeries P hr hα0 hint x]
        with ω hω
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦ mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω
    _ < ⊤ := hint x

private theorem integrable_discountedStoppedSum
    {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    Integrable (discountedStoppedSum α r τ) (markovChainMeasure P x) := by
  apply (integrable_discountedAbsSeries P hr hα0 hint x).mono
    (measurable_discountedStoppedSum hr hτ).aestronglyMeasurable
  filter_upwards [ae_summable_discountedAbsSeries P hr hα0 hint x]
    with ω hω
  let f : ℕ → ℝ :=
    fun t ↦ if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0
  have hnorm : ∀ t, ‖f t‖ ≤ α ^ t * |r (ω t)| := by
    intro t
    by_cases ht : (t : ℕ∞) < τ ω
    · simp [f, ht, abs_mul, abs_pow, abs_of_nonneg hα0]
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

private theorem ae_norm_discountedStoppedSum_le_absSeries
    {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S)
    {τ : (ℕ → S) → ℕ∞} :
    ∀ᵐ ω ∂markovChainMeasure P x,
      ‖discountedStoppedSum α r τ ω‖ ≤
        ∑' t : ℕ, α ^ t * |r (ω t)| := by
  filter_upwards [ae_summable_discountedAbsSeries P hr hα0 hint x]
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

private theorem summable_discountedStoppedSum_one
    {S : Type*} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun t : ℕ ↦
      if (t : ℕ∞) < τ ω then α ^ t * (1 : ℝ) else 0) := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_norm_lt_one (K := ℝ) (by
      rw [Real.norm_eq_abs, abs_of_nonneg hα0]
      exact hα1))
  intro t
  by_cases ht : (t : ℕ∞) < τ ω
  · simp [ht, abs_pow, abs_of_nonneg hα0]
  · simp [ht, pow_nonneg hα0 t]

private theorem discountedStoppedSum_one_ge_one
    {S : Type*} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : (ℕ → S) → ℕ∞} (hτ1 : ∀ ω, 1 ≤ τ ω) (ω : ℕ → S) :
    1 ≤ discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ ω := by
  let f : ℕ → ℝ :=
    fun t ↦ if (t : ℕ∞) < τ ω then α ^ t * (1 : ℝ) else 0
  have hfsum : Summable f :=
    summable_discountedStoppedSum_one hα0 hα1 τ ω
  rw [show discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ ω =
      ∑' t, f t by rfl, hfsum.tsum_eq_zero_add]
  have h0 : (0 : ℕ∞) < τ ω := lt_of_lt_of_le (by norm_num) (hτ1 ω)
  have htail : 0 ≤ ∑' t : ℕ, f (t + 1) :=
    tsum_nonneg fun t ↦ by
      unfold f
      split_ifs
      · positivity
      · positivity
  simpa [f, h0] using add_le_add_left htail 1

private theorem integrable_discountedStoppedSum_one
    {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    Integrable (discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ)
      (markovChainMeasure P x) := by
  letI : IsProbabilityMeasure (markovChainMeasure P x) := by
    rw [markovChainMeasure]
    infer_instance
  have hgeom : Summable (fun t : ℕ ↦ α ^ t) :=
    summable_geometric_of_norm_lt_one (K := ℝ) (by
      rw [Real.norm_eq_abs, abs_of_nonneg hα0]
      exact hα1)
  apply (integrable_const (∑' t : ℕ, α ^ t)).mono
    (measurable_discountedStoppedSum measurable_const hτ).aestronglyMeasurable
  filter_upwards with ω
  let f : ℕ → ℝ :=
    fun t ↦ if (t : ℕ∞) < τ ω then α ^ t * (1 : ℝ) else 0
  have hnorm : ∀ t, ‖f t‖ ≤ α ^ t := by
    intro t
    by_cases ht : (t : ℕ∞) < τ ω
    · simp [f, ht, abs_pow, abs_of_nonneg hα0]
    · simp [f, ht, pow_nonneg hα0 t]
  have hfsum := summable_discountedStoppedSum_one hα0 hα1 τ ω
  calc
    ‖discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ ω‖ =
        ‖∑' t, f t‖ := rfl
    _ ≤ ∑' t, ‖f t‖ := norm_tsum_le_tsum_norm hfsum.norm
    _ ≤ ∑' t, α ^ t := hfsum.norm.tsum_le_tsum hnorm hgeom
    _ = ‖∑' t, α ^ t‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact tsum_nonneg fun t ↦ pow_nonneg hα0 t

private theorem integral_discountedStoppedSum_one_ge_one
    {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ)
    (hτ1 : ∀ ω, 1 ≤ τ ω) :
    1 ≤ ∫ ω, discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ ω
      ∂markovChainMeasure P x := by
  letI : IsProbabilityMeasure (markovChainMeasure P x) := by
    rw [markovChainMeasure]
    infer_instance
  have hmono := integral_mono (integrable_const (1 : ℝ))
    (integrable_discountedStoppedSum_one P hα0 hα1 x hτ)
    (fun ω ↦ discountedStoppedSum_one_ge_one hα0 hα1 hτ1 ω)
  simpa using hmono

private theorem gittinsRatioSet_bddAbove
    {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    BddAbove {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞,
      IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      g = (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x) /
          (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω
            ∂markovChainMeasure P x)} := by
  let M : ℝ :=
    ∫ ω, (∑' t : ℕ, α ^ t * |r (ω t)|) ∂markovChainMeasure P x
  refine ⟨M, ?_⟩
  rintro g ⟨τ, hτ, hτ1, rfl⟩
  have hα0' : 0 ≤ α := hα0.le
  have hM0 : 0 ≤ M := by
    apply integral_nonneg
    intro ω
    exact tsum_nonneg fun t ↦
      mul_nonneg (pow_nonneg hα0' t) (abs_nonneg _)
  have hnum :
      |∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x| ≤ M := by
    simpa [M, Real.norm_eq_abs] using
      norm_integral_le_of_norm_le
        (integrable_discountedAbsSeries P hr hα0' hint x)
        (ae_norm_discountedStoppedSum_le_absSeries P hr hα0' hint x
          (τ := τ))
  have hden :
      1 ≤ ∫ ω, discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ ω
        ∂markovChainMeasure P x :=
    integral_discountedStoppedSum_one_ge_one P hα0' hα1 x hτ hτ1
  have hden0 :
      0 < ∫ ω, discountedStoppedSum α (fun _ : S ↦ (1 : ℝ)) τ ω
        ∂markovChainMeasure P x :=
    lt_of_lt_of_le zero_lt_one hden
  rw [div_le_iff₀ hden0]
  nlinarith [le_abs_self
    (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x)]

end BanditAlgorithm

open BanditAlgorithm

/-- Every admissible stopping-time reward ratio is bounded by the Gittins
index, directly from the supremum definition (L&S Eq. (35.9)). -/
theorem solution
    {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) (x : S)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ)
    (hτ1 : ∀ ω, 1 ≤ τ ω) :
    (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P x) /
        (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω
          ∂markovChainMeasure P x) ≤
      gittinsIndex P r α x := by
  rw [gittinsIndex]
  apply le_csSup (gittinsRatioSet_bddAbove P hr hα0 hα1 hint x)
  exact ⟨τ, hτ, hτ1, rfl⟩
