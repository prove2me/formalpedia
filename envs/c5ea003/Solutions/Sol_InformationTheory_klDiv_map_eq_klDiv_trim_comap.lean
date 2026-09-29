-- Prove2me | solution 1 for InformationTheory.klDiv_map_eq_klDiv_trim_comap
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T16:09:43.789472+00:00
-- url     : https://prove2.me/submissions/82224206-f98f-46b9-969e-bb8335b7e1cf

import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Relative entropy between push-forward measures

For a measurable `φ : α → β`, the divergence between the push-forwards of `μ` and `ν` along `φ`
equals the divergence computed on the σ-algebra `φ` generates:

`klDiv (μ.map φ) (ν.map φ) = klDiv (μ.trim hφ.comap_le) (ν.trim hφ.comap_le)`.

This is L&S Exercise 14.9 (printed p. 195). It is the bridge between "observe a random element"
and "restrict to a sub-σ-algebra": the two ways of forgetting information agree.
-/

open MeasureTheory InformationTheory Set
open scoped ENNReal

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

theorem solution {φ : α → β} (hφ : Measurable φ) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map φ) (ν.map φ) =
      @klDiv α (mβ.comap φ) (μ.trim hφ.comap_le) (ν.trim hφ.comap_le) := by
  classical
  haveI : IsFiniteMeasure (μ.map φ) := ⟨by
    rw [Measure.map_apply hφ MeasurableSet.univ]; exact measure_lt_top μ _⟩
  haveI : IsFiniteMeasure (ν.map φ) := ⟨by
    rw [Measure.map_apply hφ MeasurableSet.univ]; exact measure_lt_top ν _⟩
  haveI : @IsFiniteMeasure α (mβ.comap φ) (μ.trim hφ.comap_le) :=
    ⟨by rw [trim_measurableSet_eq hφ.comap_le MeasurableSet.univ]; exact measure_lt_top μ univ⟩
  haveI : @IsFiniteMeasure α (mβ.comap φ) (ν.trim hφ.comap_le) :=
    ⟨by rw [trim_measurableSet_eq hφ.comap_le MeasurableSet.univ]; exact measure_lt_top ν univ⟩
  -- the trimmed measure is the preimage measure
  have htrim : ∀ (ρ : Measure α) (B : Set β), MeasurableSet B →
      (ρ.trim hφ.comap_le) (φ ⁻¹' B) = (ρ.map φ) B := by
    intro ρ B hB
    rw [trim_measurableSet_eq hφ.comap_le ⟨B, hB, rfl⟩, Measure.map_apply hφ hB]
  by_cases hac : (μ.map φ) ≪ (ν.map φ)
  swap
  · -- both sides are `⊤`
    rw [klDiv_of_not_ac hac, klDiv_of_not_ac]
    intro hac'
    refine hac (Measure.AbsolutelyContinuous.mk fun B hB hνB ↦ ?_)
    rw [← htrim μ B hB]
    exact hac' (by rw [htrim ν B hB]; exact hνB)
  -- the density on the comap σ-algebra is the pulled-back density
  set g : β → ℝ≥0∞ := (μ.map φ).rnDeriv (ν.map φ) with hg
  have hg_meas : Measurable g := Measure.measurable_rnDeriv _ _
  have hgφ_meas : Measurable[mβ.comap φ] (g ∘ φ) := hg_meas.comp (Measurable.of_comap_le le_rfl)
  have key : μ.trim hφ.comap_le = (ν.trim hφ.comap_le).withDensity (g ∘ φ) := by
    refine @Measure.ext _ (mβ.comap φ) _ _ (fun A hA ↦ ?_)
    obtain ⟨B, hB, rfl⟩ := hA
    have hpre : MeasurableSet[mβ.comap φ] (φ ⁻¹' B) := ⟨B, hB, rfl⟩
    rw [withDensity_apply _ hpre, htrim μ B hB]
    calc (μ.map φ) B = ∫⁻ y in B, g y ∂(ν.map φ) := (Measure.setLIntegral_rnDeriv hac _).symm
      _ = ∫⁻ y, B.indicator g y ∂(ν.map φ) := by rw [lintegral_indicator hB]
      _ = ∫⁻ x, B.indicator g (φ x) ∂ν := by
            rw [lintegral_map (hg_meas.indicator hB) hφ]
      _ = ∫⁻ x, (φ ⁻¹' B).indicator (g ∘ φ) x ∂ν := by
            refine lintegral_congr fun x ↦ ?_
            by_cases hx : φ x ∈ B <;> simp [Set.indicator_apply, hx, Function.comp]
      _ = ∫⁻ x, (φ ⁻¹' B).indicator (g ∘ φ) x ∂(ν.trim hφ.comap_le) :=
            (lintegral_trim hφ.comap_le (hgφ_meas.indicator hpre)).symm
      _ = ∫⁻ x in φ ⁻¹' B, (g ∘ φ) x ∂(ν.trim hφ.comap_le) := by
            rw [lintegral_indicator hpre]
  -- transfer absolute continuity and the log-likelihood ratio
  have hac₂ : μ.trim hφ.comap_le ≪ ν.trim hφ.comap_le := by
    rw [key]; exact withDensity_absolutelyContinuous _ _
  have hrn : (μ.trim hφ.comap_le).rnDeriv (ν.trim hφ.comap_le) =ᵐ[ν.trim hφ.comap_le] g ∘ φ := by
    rw [key]; exact Measure.rnDeriv_withDensity _ hgφ_meas
  have hllr : llr (μ.trim hφ.comap_le) (ν.trim hφ.comap_le)
      =ᵐ[μ.trim hφ.comap_le] fun x ↦ Real.log ((g ∘ φ) x).toReal := by
    filter_upwards [hac₂ hrn] with x hx
    simp only [llr_def, hx]
  -- integrability matches on both sides
  have hint_iff : Integrable (llr (μ.map φ) (ν.map φ)) (μ.map φ) ↔
      Integrable (llr (μ.trim hφ.comap_le) (ν.trim hφ.comap_le)) (μ.trim hφ.comap_le) := by
    constructor
    · intro hI
      refine Integrable.congr ?_ hllr.symm
      have h1 : Integrable (fun x ↦ Real.log (g (φ x)).toReal) μ := by
        rw [show (fun x ↦ Real.log (g (φ x)).toReal) = (fun y ↦ Real.log (g y).toReal) ∘ φ from rfl]
        exact (integrable_map_measure
          ((hg_meas.ennreal_toReal.log).aestronglyMeasurable) hφ.aemeasurable).mp hI
      exact h1.trim hφ.comap_le (hgφ_meas.ennreal_toReal.log).stronglyMeasurable
    · intro hI
      have h1 : Integrable (fun x ↦ Real.log ((g ∘ φ) x).toReal) (μ.trim hφ.comap_le) :=
        hI.congr hllr
      have h2 : Integrable (fun x ↦ Real.log ((g ∘ φ) x).toReal) μ :=
        integrable_of_integrable_trim hφ.comap_le h1
      exact (integrable_map_measure
        ((hg_meas.ennreal_toReal.log).aestronglyMeasurable) hφ.aemeasurable).mpr h2
  by_cases hint : Integrable (llr (μ.map φ) (ν.map φ)) (μ.map φ)
  swap
  · rw [klDiv_of_not_integrable hint, klDiv_of_not_integrable (fun h ↦ hint (hint_iff.mpr h))]
  rw [klDiv_of_ac_of_integrable hac hint,
    klDiv_of_ac_of_integrable hac₂ (hint_iff.mp hint)]
  congr 1
  have hI : ∫ y, llr (μ.map φ) (ν.map φ) y ∂(μ.map φ)
      = ∫ x, llr (μ.trim hφ.comap_le) (ν.trim hφ.comap_le) x ∂(μ.trim hφ.comap_le) := by
    have e1 : ∫ y, llr (μ.map φ) (ν.map φ) y ∂(μ.map φ) = ∫ x, Real.log ((g ∘ φ) x).toReal ∂μ :=
      integral_map hφ.aemeasurable (hg_meas.ennreal_toReal.log).aestronglyMeasurable
    have e2 : ∫ x, llr (μ.trim hφ.comap_le) (ν.trim hφ.comap_le) x ∂(μ.trim hφ.comap_le)
        = ∫ x, Real.log ((g ∘ φ) x).toReal ∂μ := by
      rw [integral_congr_ae hllr]
      exact (integral_trim (μ := μ) hφ.comap_le
        (hgφ_meas.ennreal_toReal.log).stronglyMeasurable).symm
    rw [e1, e2]
  rw [hI]
  congr 1
  · simp [measureReal_def, trim_measurableSet_eq hφ.comap_le MeasurableSet.univ,
      Measure.map_apply hφ MeasurableSet.univ]
  · simp [measureReal_def, trim_measurableSet_eq hφ.comap_le MeasurableSet.univ,
      Measure.map_apply hφ MeasurableSet.univ]
