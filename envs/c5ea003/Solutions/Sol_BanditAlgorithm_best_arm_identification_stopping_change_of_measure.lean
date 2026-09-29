-- Prove2me | solution 1 for BanditAlgorithm.best_arm_identification_stopping_change_of_measure
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T19:28:14.215585+00:00
-- url     : https://prove2.me/submissions/c19eabc2-8751-4df4-b92f-35bdb03bfb58

import Theorems.Thm_BanditAlgorithm_bandit_stopped_binary_testing_information_lower_bound

open MeasureTheory ProbabilityTheory InformationTheory ENNReal
open BanditAlgorithm

theorem solution {k : ℕ}
    (𝓔 : Set (StochasticBandit k)) (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (π : BanditPolicy k) (τ : (ℕ → Fin k × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin k × ℝ) → Fin k)
    (hτ : IsBanditStoppingTime τ) (hψ : Measurable[hτ.measurableSpace] ψ)
    (hsound : IsSoundBAI δ π τ ψ 𝓔)
    (ν ν' : StochasticBandit k) (hν : ν ∈ 𝓔)
    (hν' : ν' ∈ baiAlternatives 𝓔 ν)
    (hfinite : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π < ⊤) :
    ENNReal.ofReal (Real.log (1 / (4 * δ))) ≤
      ∑ i, (∫⁻ ω, ∑' t : ℕ,
          if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0
        ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i) := by
  classical
  let A : Set (ℕ → Fin k × ℝ) :=
    {ω | τ ω < ⊤ ∧ ψ ω ∈ banditOptimalArms ν}
  have hA : Measurable[hτ.measurableSpace] A := by
    dsimp [A]
    change @Measurable (ℕ → Fin k × ℝ) Prop hτ.measurableSpace _
      (fun ω ↦ τ ω < ⊤ ∧ ψ ω ∈ banditOptimalArms ν)
    have hstop : @Measurable (ℕ → Fin k × ℝ) (WithTop ℕ)
        hτ.measurableSpace WithTop.instMeasurableSpace τ := hτ.measurable
    have hstopPred : @Measurable (ℕ → Fin k × ℝ) Prop
        hτ.measurableSpace _ (fun ω ↦ τ ω < ⊤) :=
      (measurable_of_countable (fun u : WithTop ℕ ↦ u < ⊤)).comp hstop
    have hoptPred : @Measurable (ℕ → Fin k × ℝ) Prop
        hτ.measurableSpace _
          (fun ω ↦ ψ ω ∈ banditOptimalArms ν) :=
      (measurable_of_countable
        (fun i : Fin k ↦ i ∈ banditOptimalArms ν)).comp hψ
    exact @Measurable.and _ hτ.measurableSpace _ _ hstopPred hoptPred
  have hτfinite : ∀ᵐ ω ∂banditTrajMeasure ν π, τ ω ≠ ⊤ := by
    have hmeas : AEMeasurable
        (fun ω : ℕ → Fin k × ℝ ↦ (τ ω : ℝ≥0∞))
        (banditTrajMeasure ν π) := by
      exact ((measurable_of_countable
        (fun u : WithTop ℕ ↦ ENat.toENNReal u)).comp
          hτ.measurable').aemeasurable
    have hlt : ∀ᵐ ω ∂banditTrajMeasure ν π, (τ ω : ℝ≥0∞) < ⊤ :=
      ae_lt_top' hmeas hfinite.ne
    filter_upwards [hlt] with ω hω
    exact (ENat.toENNReal_ne_top.mp hω.ne)
  have hnever : banditTrajMeasure ν π {ω | τ ω = ⊤} = 0 := by
    exact measure_eq_zero_iff_ae_notMem.mpr
      (hτfinite.mono fun ω hω hmem ↦ hω hmem)
  have hgap_of_not_opt (ξ : StochasticBandit k) (i : Fin k)
      (hi : i ∉ banditOptimalArms ξ) : 0 < banditGap ξ i := by
    have hle : banditArmMean ξ i ≤ banditOptimalMean ξ := by
      unfold banditOptimalMean
      exact le_ciSup (Set.finite_range (fun j : Fin k ↦ banditArmMean ξ j)).bddAbove i
    have hne : banditArmMean ξ i ≠ banditOptimalMean ξ := by
      simpa [banditOptimalArms] using hi
    rw [banditGap]
    exact sub_pos.mpr (lt_of_le_of_ne hle hne)
  have hνerrENN :
      banditTrajMeasure ν π Aᶜ ≤ ENNReal.ofReal δ := by
    let B : Set (ℕ → Fin k × ℝ) :=
      {ω | τ ω < ⊤ ∧ 0 < banditGap ν (ψ ω)}
    have hsubset : Aᶜ ⊆ {ω | τ ω = ⊤} ∪ B := by
      intro ω hω
      by_cases hstop : τ ω = ⊤
      · exact Or.inl hstop
      · right
        constructor
        · exact lt_top_iff_ne_top.mpr hstop
        · apply hgap_of_not_opt
          intro hopt
          exact hω ⟨lt_top_iff_ne_top.mpr hstop, hopt⟩
    calc
      banditTrajMeasure ν π Aᶜ ≤
          banditTrajMeasure ν π ({ω | τ ω = ⊤} ∪ B) :=
        measure_mono hsubset
      _ ≤ banditTrajMeasure ν π {ω | τ ω = ⊤} +
          banditTrajMeasure ν π B := measure_union_le _ _
      _ = banditTrajMeasure ν π B := by rw [hnever, zero_add]
      _ ≤ ENNReal.ofReal δ := hsound ν hν
  have hν'errENN :
      banditTrajMeasure ν' π A ≤ ENNReal.ofReal δ := by
    have hsubset : A ⊆
        {ω | τ ω < ⊤ ∧ 0 < banditGap ν' (ψ ω)} := by
      intro ω hω
      refine ⟨hω.1, hgap_of_not_opt ν' (ψ ω) ?_⟩
      intro hopt'
      exact hν'.2.le_bot ⟨hopt', hω.2⟩
    calc
      banditTrajMeasure ν' π A ≤
          banditTrajMeasure ν' π
            {ω | τ ω < ⊤ ∧ 0 < banditGap ν' (ψ ω)} :=
        measure_mono hsubset
      _ ≤ ENNReal.ofReal δ := hsound ν' hν'.1
  have hδ0 : 0 ≤ δ := hδ.1.le
  have hνerr : (banditTrajMeasure ν π).real Aᶜ ≤ δ := by
    rw [Measure.real]
    calc
      (banditTrajMeasure ν π Aᶜ).toReal ≤
          (ENNReal.ofReal δ).toReal :=
        ENNReal.toReal_mono (by finiteness) hνerrENN
      _ = δ := ENNReal.toReal_ofReal hδ0
  have hν'err : (banditTrajMeasure ν' π).real A ≤ δ := by
    rw [Measure.real]
    calc
      (banditTrajMeasure ν' π A).toReal ≤
          (ENNReal.ofReal δ).toReal :=
        ENNReal.toReal_mono (by finiteness) hν'errENN
      _ = δ := ENNReal.toReal_ofReal hδ0
  exact bandit_stopped_binary_testing_information_lower_bound
    δ hδ ν ν' π τ hτ hfinite A hA hνerr hν'err
