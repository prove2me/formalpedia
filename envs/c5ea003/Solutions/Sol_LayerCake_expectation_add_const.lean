-- Prove2me | solution 1 for LayerCake.expectation_add_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T00:25:28.930067+00:00
-- url     : https://prove2.me/submissions/afb3442e-11af-4712-af88-f9423294b085

import Theorems.Thm_LayerCake_bounded_layercake_identity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ)
    (hWm : Measurable W) (M : ℝ) (hWb : ∀ ω, |W ω| ≤ M) :
    ∫ ω, (W ω + M) ∂P
      = ∫ t in Set.Icc (-M) M, (P {ω | W ω > t}).toReal := by
  have hS_meas : MeasurableSet {(p : Ω × ℝ) | W p.1 > p.2} :=
    measurableSet_lt measurable_snd (hWm.comp measurable_fst)
  have hF_meas : Measurable
      (fun p : Ω × ℝ => Set.indicator (Set.Iio (W p.1)) (1 : ℝ → ℝ) p.2) := by
    have heq : (fun p : Ω × ℝ => Set.indicator (Set.Iio (W p.1)) (1 : ℝ → ℝ) p.2)
        = Set.indicator {(p : Ω × ℝ) | W p.1 > p.2} (fun _ => (1 : ℝ)) := by
      funext p
      by_cases h : W p.1 > p.2
      · have hm : p.2 ∈ Set.Iio (W p.1) := Set.mem_Iio.2 h
        have h2 : p ∈ {(p : Ω × ℝ) | W p.1 > p.2} := h
        simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
      · have hm : p.2 ∉ Set.Iio (W p.1) := by
          simpa [Set.mem_Iio] using h
        have h2 : p ∉ {(p : Ω × ℝ) | W p.1 > p.2} := h
        simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
    rw [heq]
    exact Measurable.indicator measurable_const hS_meas
  have hIcc_fin : volume (Set.Icc (-M) M) < ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  haveI : Fact (volume (Set.Icc (-M) M) < ∞) := ⟨hIcc_fin⟩
  have hF_bdd : ∀ᵐ p : Ω × ℝ ∂(P.prod (volume.restrict (Set.Icc (-M) M))),
      ‖Set.indicator (Set.Iio (W p.1)) (1 : ℝ → ℝ) p.2‖ ≤ 1 := by
    filter_upwards with p
    by_cases h : W p.1 > p.2
    · have hm : p.2 ∈ Set.Iio (W p.1) := Set.mem_Iio.2 h
      rw [Set.indicator_of_mem hm]
      simp
    · have hm : p.2 ∉ Set.Iio (W p.1) := by
        simpa [Set.mem_Iio] using h
      rw [Set.indicator_of_notMem hm]
      simp
  have hF_int : Integrable
      (fun p : Ω × ℝ => Set.indicator (Set.Iio (W p.1)) (1 : ℝ → ℝ) p.2)
      (P.prod (volume.restrict (Set.Icc (-M) M))) :=
    Integrable.of_bound hF_meas.aestronglyMeasurable 1 hF_bdd
  have hW_eq : ∀ ω : Ω, W ω + M
      = ∫ t in Set.Icc (-M) M, Set.indicator (Set.Iio (W ω)) 1 t :=
    fun ω => LayerCake.bounded_layercake_identity (W ω) M (hWb ω)
  have hAt_amb : ∀ t : ℝ, MeasurableSet {ω | W ω > t} :=
    fun t => hWm measurableSet_Ioi
  have hF_unc : Integrable
      (Function.uncurry fun ω t => Set.indicator (Set.Iio (W ω)) (1 : ℝ → ℝ) t)
      (P.prod (volume.restrict (Set.Icc (-M) M))) := hF_int
  have hswap := integral_integral_swap hF_unc
  have hLHS : (∫ ω, ∫ t, Set.indicator (Set.Iio (W ω)) 1 t
      ∂(volume.restrict (Set.Icc (-M) M)) ∂P)
      = ∫ ω, (W ω + M) ∂P := by
    apply integral_congr_ae
    filter_upwards with ω
    exact (hW_eq ω).symm
  have hRHS : (∫ t, ∫ ω, Set.indicator (Set.Iio (W ω)) 1 t ∂P
      ∂(volume.restrict (Set.Icc (-M) M)))
      = ∫ t in Set.Icc (-M) M, (P {ω | W ω > t}).toReal := by
    apply integral_congr_ae
    filter_upwards with t
    have heq : (fun ω => Set.indicator (Set.Iio (W ω)) 1 t)
        = Set.indicator {ω | W ω > t} (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h : W ω > t
      · have hm : t ∈ Set.Iio (W ω) := Set.mem_Iio.2 h
        have h2 : ω ∈ {ω | W ω > t} := h
        simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
      · have hm : t ∉ Set.Iio (W ω) := by
          simpa [Set.mem_Iio] using h
        have h2 : ω ∉ {ω | W ω > t} := h
        simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
    rw [heq, integral_indicator_const _ (hAt_amb t)]
    simp [Measure.real_def]
  rw [← hLHS, hswap]
  exact hRHS
