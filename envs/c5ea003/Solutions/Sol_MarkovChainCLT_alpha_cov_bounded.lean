-- Prove2me | solution 1 for MarkovChainCLT.alpha_cov_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T00:50:17.908697+00:00
-- url     : https://prove2.me/submissions/2edbd8b9-2d77-478c-9bc8-985202cb4c62

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_alpha_indicator_cov_le
import Theorems.Thm_MarkovChainCLT_processSigma_le_of_measurable
import Theorems.Thm_LayerCake_bounded_layercake_identity
import Theorems.Thm_LayerCake_expectation_add_const
import Theorems.Thm_ProbabilityTheory_cov_indicator_eq
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory ProbabilityTheory MarkovChainCLT Filter
open scoped ProbabilityTheory ENNReal Topology

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E)
    (hY : ∀ n, Measurable (Y n)) (n k : ℕ) (U V : Ω → ℝ)
    (hU : Measurable[processSigma Y (Set.Iic k)] U)
    (hV : Measurable[processSigma Y (Set.Ici (k + n))] V)
    (M : ℝ) (hM0 : 0 ≤ M) (hUb : ∀ ω, |U ω| ≤ M) (hVb : ∀ ω, |V ω| ≤ M) :
    |cov[U, V; P]| ≤ 4 * M ^ 2 * alphaMixingCoef P Y n := by
  -- Stage 1: past/future sit below ambient; U, V are ambient-measurable and L².
  have hle_past : processSigma Y (Set.Iic k) ≤ ‹MeasurableSpace Ω› :=
    MarkovChainCLT.processSigma_le_of_measurable Y hY _
  have hle_fut : processSigma Y (Set.Ici (k + n)) ≤ ‹MeasurableSpace Ω› :=
    MarkovChainCLT.processSigma_le_of_measurable Y hY _
  have hUm : Measurable U := hU.mono hle_past le_rfl
  have hVm : Measurable V := hV.mono hle_fut le_rfl
  have hU2 : MemLp U 2 P :=
    MemLp.of_bound hUm.aestronglyMeasurable M
      (by filter_upwards with ω using hUb ω)
  have hV2 : MemLp V 2 P :=
    MemLp.of_bound hVm.aestronglyMeasurable M
      (by filter_upwards with ω using hVb ω)
  -- Stage 2: superlevel sets are past/future-measurable; per-(t,s) alpha bound.
  have hAt : ∀ t : ℝ, MeasurableSet[processSigma Y (Set.Iic k)] {ω | U ω > t} :=
    fun t => hU measurableSet_Ioi
  have hBs : ∀ s : ℝ, MeasurableSet[processSigma Y (Set.Ici (k + n))] {ω | V ω > s} :=
    fun s => hV measurableSet_Ioi
  have hα_ts : ∀ t s : ℝ,
      |(P ({ω | U ω > t} ∩ {ω | V ω > s})).toReal
        - (P {ω | U ω > t}).toReal * (P {ω | V ω > s}).toReal|
        ≤ alphaMixingCoef P Y n :=
    fun t s => MarkovChainCLT.alpha_indicator_cov_le P Y n k _ _ (hAt t) (hBs s)
  -- Stage 3: joint measurability on the product; layer-cake instances.
  have hS_meas : MeasurableSet {(p : Ω × ℝ) | U p.1 > p.2} :=
    measurableSet_lt measurable_snd (hUm.comp measurable_fst)
  have hT_meas : MeasurableSet {(p : Ω × ℝ) | V p.1 > p.2} :=
    measurableSet_lt measurable_snd (hVm.comp measurable_fst)
  -- Stage 13: V-side joint measurability for the triple integrand.
  have hG_meas : Measurable (fun p : Ω × ℝ => Set.indicator (Set.Iio (V p.1)) (1 : ℝ → ℝ) p.2) := by
    have heqG : (fun p : Ω × ℝ => Set.indicator (Set.Iio (V p.1)) (1 : ℝ → ℝ) p.2)
        = Set.indicator {(p : Ω × ℝ) | V p.1 > p.2} (fun _ => (1 : ℝ)) := by
      funext p
      by_cases h : V p.1 > p.2
      · have hm : p.2 ∈ Set.Iio (V p.1) := Set.mem_Iio.2 h
        have h2 : p ∈ {(p : Ω × ℝ) | V p.1 > p.2} := h
        simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
      · have hm : p.2 ∉ Set.Iio (V p.1) := by
          simpa [Set.mem_Iio] using h
        have h2 : p ∉ {(p : Ω × ℝ) | V p.1 > p.2} := h
        simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
    rw [heqG]
    exact Measurable.indicator measurable_const hT_meas
  -- Stage 4: layer-cake integrands on the product; E[U+M] via Fubini.
  -- F(ω,t) = 1_{Uω > t}, jointly measurable, bounded.
  have hF_meas : Measurable (fun p : Ω × ℝ => Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2) := by
    have heq : (fun p : Ω × ℝ => Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2)
        = Set.indicator {(p : Ω × ℝ) | U p.1 > p.2} (fun _ => (1 : ℝ)) := by
      funext p
      by_cases h : U p.1 > p.2
      · have h2 : p ∈ {(p : Ω × ℝ) | U p.1 > p.2} := h
        have hm : p.2 ∈ Set.Iio (U p.1) := Set.mem_Iio.2 h
        simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
      · have h2 : p ∉ {(p : Ω × ℝ) | U p.1 > p.2} := h
        have hm : p.2 ∉ Set.Iio (U p.1) := by
          simpa [Set.mem_Iio] using h
        simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
    rw [heq]
    exact Measurable.indicator measurable_const hS_meas
  -- Stage 5: finite product measure; Fubini-ready integrability.
  have hIcc_fin : volume (Set.Icc (-M) M) < ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  haveI : Fact (volume (Set.Icc (-M) M) < ∞) := ⟨hIcc_fin⟩
  -- Stage 6: F is integrable on P × (vol restricted to Icc); E[U+M] swap.
  have hF_bdd : ∀ᵐ p : Ω × ℝ ∂(P.prod (volume.restrict (Set.Icc (-M) M))),
      ‖Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2‖ ≤ 1 := by
    filter_upwards with p
    by_cases h : U p.1 > p.2
    · have hm : p.2 ∈ Set.Iio (U p.1) := Set.mem_Iio.2 h
      rw [Set.indicator_of_mem hm]
      simp
    · have hm : p.2 ∉ Set.Iio (U p.1) := by
        simpa [Set.mem_Iio] using h
      rw [Set.indicator_of_notMem hm]
      simp
  have hF_int : Integrable
      (fun p : Ω × ℝ => Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2)
      (P.prod (volume.restrict (Set.Icc (-M) M))) :=
    Integrable.of_bound hF_meas.aestronglyMeasurable 1 hF_bdd
  -- Stage 7: E[U+M] = ∫_{Icc} P(U>t) via pointwise layer-cake + Fubini.
  have hUM_eq : ∀ ω : Ω, U ω + M
      = ∫ t in Set.Icc (-M) M, Set.indicator (Set.Iio (U ω)) 1 t :=
    fun ω => LayerCake.bounded_layercake_identity (U ω) M (hUb ω)
  -- Stage 8: E[U+M] = ∫_{Icc} P(U>t) by Fubini.
  have hAt_amb : ∀ t : ℝ, MeasurableSet {ω | U ω > t} :=
    fun t => hUm measurableSet_Ioi
  have hBs_amb : ∀ s : ℝ, MeasurableSet {ω | V ω > s} :=
    fun s => hVm measurableSet_Ioi
  have hEU : ∫ ω, (U ω + M) ∂P
      = ∫ t in Set.Icc (-M) M, (P {ω | U ω > t}).toReal := by
    have hF_unc : Integrable
        (Function.uncurry fun ω t => Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t)
        (P.prod (volume.restrict (Set.Icc (-M) M))) := hF_int
    have hswap := integral_integral_swap hF_unc
    -- LHS of swap: ∫ ω, ∫ t in Icc, F = E[U+M] by layer-cake
    have hLHS : (∫ ω, ∫ t, Set.indicator (Set.Iio (U ω)) 1 t
        ∂(volume.restrict (Set.Icc (-M) M)) ∂P)
        = ∫ ω, (U ω + M) ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      exact (hUM_eq ω).symm
    -- RHS of swap: ∫ t in Icc, ∫ ω, F = ∫ P(A_t)
    have hRHS : (∫ t, ∫ ω, Set.indicator (Set.Iio (U ω)) 1 t ∂P
        ∂(volume.restrict (Set.Icc (-M) M)))
        = ∫ t in Set.Icc (-M) M, (P {ω | U ω > t}).toReal := by
      apply integral_congr_ae
      filter_upwards with t
      have heq : (fun ω => Set.indicator (Set.Iio (U ω)) 1 t)
          = Set.indicator {ω | U ω > t} (fun _ => (1 : ℝ)) := by
        funext ω
        by_cases h : U ω > t
        · have hm : t ∈ Set.Iio (U ω) := Set.mem_Iio.2 h
          have h2 : ω ∈ {ω | U ω > t} := h
          simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
        · have hm : t ∉ Set.Iio (U ω) := by
            simpa [Set.mem_Iio] using h
          have h2 : ω ∉ {ω | U ω > t} := h
          simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
      rw [heq, integral_indicator_const _ (hAt_amb t)]
      simp [Measure.real_def]
    rw [hLHS] at hswap
    rw [hswap]
    exact hRHS
  -- Stage 9: tail-probability map is antitone, hence measurable.
  have hPtail_anti : Antitone (fun t : ℝ => (P {ω | U ω > t}).toReal) := by
    intro a b hab
    apply ENNReal.toReal_mono (measure_ne_top P _)
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact lt_of_le_of_lt hab hω
  have hPtail_meas : Measurable (fun t : ℝ => (P {ω | U ω > t}).toReal) :=
    hPtail_anti.measurable
  -- Stage 10: centered per-ω representation.
  have hcenterU : ∀ ω : Ω, (U ω + M) - (∫ ω', (U ω' + M) ∂P)
      = ∫ t in Set.Icc (-M) M,
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal) := by
    intro ω
    have hFb : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (-M) M)),
        ‖Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t‖ ≤ 1 := by
      filter_upwards with t
      by_cases h : t ∈ Set.Iio (U ω)
      · rw [Set.indicator_of_mem h]
        simp
      · rw [Set.indicator_of_notMem h]
        simp
    have hF1 : Integrable (fun t => Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t)
        (volume.restrict (Set.Icc (-M) M)) :=
      Integrable.of_bound
        (Measurable.indicator measurable_const measurableSet_Iio).aestronglyMeasurable
        1 hFb
    have hPb : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (-M) M)),
        ‖(P {ω | U ω > t}).toReal‖ ≤ 1 := by
      filter_upwards with t
      calc ‖(P {ω | U ω > t}).toReal‖
          = |(P {ω | U ω > t}).toReal| := Real.norm_eq_abs _
        _ ≤ 1 := by
          have hle2 : (P {ω | U ω > t}).toReal ≤ 1 := by
            have hle : P {ω | U ω > t} ≤ 1 := by
              calc P {ω | U ω > t} ≤ P Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
            exact ENNReal.toReal_mono (by simp) hle
          have nn : 0 ≤ (P {ω | U ω > t}).toReal := ENNReal.toReal_nonneg
          rw [abs_of_nonneg nn]
          exact hle2
    have hP1 : Integrable (fun t => (P {ω | U ω > t}).toReal)
        (volume.restrict (Set.Icc (-M) M)) :=
      Integrable.of_bound hPtail_meas.aestronglyMeasurable 1 hPb
    rw [hUM_eq ω, hEU, ← integral_sub hF1 hP1]
  -- Stage 11: V-side expectation + centered representation.
  have hEV : ∫ ω, (V ω + M) ∂P
      = ∫ s in Set.Icc (-M) M, (P {ω | V ω > s}).toReal :=
    LayerCake.expectation_add_const P V hVm M (fun ω => hVb ω)
  have hQtail_anti : Antitone (fun s : ℝ => (P {ω | V ω > s}).toReal) := by
    intro a b hab
    apply ENNReal.toReal_mono (measure_ne_top P _)
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact lt_of_le_of_lt hab hω
  have hQtail_meas : Measurable (fun s : ℝ => (P {ω | V ω > s}).toReal) :=
    hQtail_anti.measurable
  have hcenterV : ∀ ω : Ω, (V ω + M) - (∫ ω', (V ω' + M) ∂P)
      = ∫ s in Set.Icc (-M) M,
        (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal) := by
    intro ω
    have hGb : ∀ᵐ s : ℝ ∂(volume.restrict (Set.Icc (-M) M)),
        ‖Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s‖ ≤ 1 := by
      filter_upwards with s
      by_cases h : s ∈ Set.Iio (V ω)
      · rw [Set.indicator_of_mem h]
        simp
      · rw [Set.indicator_of_notMem h]
        simp
    have hG1 : Integrable (fun s => Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s)
        (volume.restrict (Set.Icc (-M) M)) :=
      Integrable.of_bound
        (Measurable.indicator measurable_const measurableSet_Iio).aestronglyMeasurable
        1 hGb
    have hQb : ∀ᵐ s : ℝ ∂(volume.restrict (Set.Icc (-M) M)),
        ‖(P {ω | V ω > s}).toReal‖ ≤ 1 := by
      filter_upwards with s
      calc ‖(P {ω | V ω > s}).toReal‖
          = |(P {ω | V ω > s}).toReal| := Real.norm_eq_abs _
        _ ≤ 1 := by
          have hle2 : (P {ω | V ω > s}).toReal ≤ 1 := by
            have hle : P {ω | V ω > s} ≤ 1 := by
              calc P {ω | V ω > s} ≤ P Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
            exact ENNReal.toReal_mono (by simp) hle
          have nn : 0 ≤ (P {ω | V ω > s}).toReal := ENNReal.toReal_nonneg
          rw [abs_of_nonneg nn]
          exact hle2
    have hQ1 : Integrable (fun s => (P {ω | V ω > s}).toReal)
        (volume.restrict (Set.Icc (-M) M)) :=
      Integrable.of_bound hQtail_meas.aestronglyMeasurable 1 hQb
    have hVM_eq : V ω + M
        = ∫ s in Set.Icc (-M) M, Set.indicator (Set.Iio (V ω)) 1 s :=
      LayerCake.bounded_layercake_identity (V ω) M (hVb ω)
    rw [hVM_eq, hEV, ← integral_sub hG1 hQ1]
  -- Stage 12: per-ω product as a double integral over Icc×Icc.
  -- A(ω) = ∫ a, B(ω) = ∫ b imply A(ω)B(ω) = ∫∫ a·b.
  have hAB_int : ∀ ω : Ω,
      ((U ω + M) - (∫ ω', (U ω' + M) ∂P)) * ((V ω + M) - (∫ ω', (V ω' + M) ∂P))
      = ∫ t in Set.Icc (-M) M, ∫ s in Set.Icc (-M) M,
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal) := by
    intro ω
    rw [hcenterU ω, hcenterV ω]
    have ha_meas : Measurable (fun t =>
        Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal) :=
      (Measurable.indicator measurable_const measurableSet_Iio).sub hPtail_meas
    have hb_meas : Measurable (fun s =>
        Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal) :=
      (Measurable.indicator measurable_const measurableSet_Iio).sub hQtail_meas
    have hab_bdd : ∀ t : ℝ,
        ‖Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t
          - (P {ω | U ω > t}).toReal‖ ≤ 2 := by
      intro t
      by_cases h : t ∈ Set.Iio (U ω)
      · rw [Set.indicator_of_mem h]
        calc ‖(1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal‖
            ≤ ‖(1 : ℝ → ℝ) t‖ + ‖(P {ω | U ω > t}).toReal‖ := norm_sub_le _ _
          _ ≤ 2 := by
            have e1 : ‖(1 : ℝ → ℝ) t‖ = 1 := by simp
            have e2 : ‖(P {ω | U ω > t}).toReal‖ ≤ 1 := by
              rw [Real.norm_eq_abs]
              have hle : (P {ω | U ω > t}).toReal ≤ 1 := by
                have hle' : P {ω | U ω > t} ≤ 1 := by
                  calc P {ω | U ω > t} ≤ P Set.univ := measure_mono (Set.subset_univ _)
                    _ = 1 := measure_univ
                exact ENNReal.toReal_mono (by simp) hle'
              have nn : 0 ≤ (P {ω | U ω > t}).toReal := ENNReal.toReal_nonneg
              rw [abs_of_nonneg nn]
              exact hle
            rw [e1]
            linarith
      · rw [Set.indicator_of_notMem h]
        have hle : (P {ω | U ω > t}).toReal ≤ 1 := by
          have hle' : P {ω | U ω > t} ≤ 1 := by
            calc P {ω | U ω > t} ≤ P Set.univ := measure_mono (Set.subset_univ _)
              _ = 1 := measure_univ
          exact ENNReal.toReal_mono (by simp) hle'
        simp only [zero_sub]
        calc ‖-(P {ω | U ω > t}).toReal‖ = |(P {ω | U ω > t}).toReal| := by
              rw [Real.norm_eq_abs, abs_neg]
          _ ≤ 2 := by
            have nn : 0 ≤ (P {ω | U ω > t}).toReal := ENNReal.toReal_nonneg
            rw [abs_of_nonneg nn]
            linarith
    -- a(t), b(s) integrable on Icc (bounded + measurable); product = double integral.
    have ha_int : Integrable (fun t =>
        Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal)
        (volume.restrict (Set.Icc (-M) M)) :=
      Integrable.of_bound ha_meas.aestronglyMeasurable 2
        (by filter_upwards with t using hab_bdd t)
    have hb_bdd : ∀ s : ℝ,
        ‖Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s
          - (P {ω | V ω > s}).toReal‖ ≤ 2 := by
      intro s
      by_cases h : s ∈ Set.Iio (V ω)
      · rw [Set.indicator_of_mem h]
        calc ‖(1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal‖
            ≤ ‖(1 : ℝ → ℝ) s‖ + ‖(P {ω | V ω > s}).toReal‖ := norm_sub_le _ _
          _ ≤ 2 := by
            have e1 : ‖(1 : ℝ → ℝ) s‖ = 1 := by simp
            have e2 : ‖(P {ω | V ω > s}).toReal‖ ≤ 1 := by
              rw [Real.norm_eq_abs]
              have hle : (P {ω | V ω > s}).toReal ≤ 1 := by
                have hle' : P {ω | V ω > s} ≤ 1 := by
                  calc P {ω | V ω > s} ≤ P Set.univ := measure_mono (Set.subset_univ _)
                    _ = 1 := measure_univ
                exact ENNReal.toReal_mono (by simp) hle'
              have nn : 0 ≤ (P {ω | V ω > s}).toReal := ENNReal.toReal_nonneg
              rw [abs_of_nonneg nn]
              exact hle
            rw [e1]
            linarith
      · rw [Set.indicator_of_notMem h]
        have hle : (P {ω | V ω > s}).toReal ≤ 1 := by
          have hle' : P {ω | V ω > s} ≤ 1 := by
            calc P {ω | V ω > s} ≤ P Set.univ := measure_mono (Set.subset_univ _)
              _ = 1 := measure_univ
          exact ENNReal.toReal_mono (by simp) hle'
        simp only [zero_sub]
        calc ‖-(P {ω | V ω > s}).toReal‖ = |(P {ω | V ω > s}).toReal| := by
              rw [Real.norm_eq_abs, abs_neg]
          _ ≤ 2 := by
            have nn : 0 ≤ (P {ω | V ω > s}).toReal := ENNReal.toReal_nonneg
            rw [abs_of_nonneg nn]
            linarith
    have hb_int : Integrable (fun s =>
        Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal)
        (volume.restrict (Set.Icc (-M) M)) :=
      Integrable.of_bound hb_meas.aestronglyMeasurable 2
        (by filter_upwards with s using hb_bdd s)
    -- (∫ a)(∫ b) = ∫∫ a·b by linearity in each variable (unconditional).
    have hprod : (∫ t in Set.Icc (-M) M,
          (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal))
        * (∫ s in Set.Icc (-M) M,
          (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal))
        = ∫ t in Set.Icc (-M) M, ∫ s in Set.Icc (-M) M,
          (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal)
          * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal) := by
      rw [← integral_mul_const _ _]
      apply integral_congr_ae
      filter_upwards with t
      rw [← integral_const_mul _ _]
    exact hprod
  -- Stage 14: triple integrand H(ω,t,s) = a(ω,t)·b(ω,s); meas + bound + int.
  have ha_bd2 : ∀ (ω : Ω) (t : ℝ),
      ‖Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) t
        - (P {ω | U ω > t}).toReal‖ ≤ 2 := by
    intro ω t
    by_cases h : t ∈ Set.Iio (U ω)
    · rw [Set.indicator_of_mem h]
      calc ‖(1 : ℝ → ℝ) t - (P {ω | U ω > t}).toReal‖
          ≤ ‖(1 : ℝ → ℝ) t‖ + ‖(P {ω | U ω > t}).toReal‖ := norm_sub_le _ _
        _ ≤ 2 := by
          have e1 : ‖(1 : ℝ → ℝ) t‖ = 1 := by simp
          have e2 : ‖(P {ω | U ω > t}).toReal‖ ≤ 1 := by
            rw [Real.norm_eq_abs]
            have hle : (P {ω | U ω > t}).toReal ≤ 1 := by
              have hle' : P {ω | U ω > t} ≤ 1 := by
                calc P {ω | U ω > t} ≤ P Set.univ := measure_mono (Set.subset_univ _)
                  _ = 1 := measure_univ
              exact ENNReal.toReal_mono (by simp) hle'
            have nn : 0 ≤ (P {ω | U ω > t}).toReal := ENNReal.toReal_nonneg
            rw [abs_of_nonneg nn]
            exact hle
          rw [e1]
          linarith
    · rw [Set.indicator_of_notMem h]
      have hle : (P {ω | U ω > t}).toReal ≤ 1 := by
        have hle' : P {ω | U ω > t} ≤ 1 := by
          calc P {ω | U ω > t} ≤ P Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        exact ENNReal.toReal_mono (by simp) hle'
      simp only [zero_sub]
      calc ‖-(P {ω | U ω > t}).toReal‖ = |(P {ω | U ω > t}).toReal| := by
            rw [Real.norm_eq_abs, abs_neg]
        _ ≤ 2 := by
          have nn : 0 ≤ (P {ω | U ω > t}).toReal := ENNReal.toReal_nonneg
          rw [abs_of_nonneg nn]
          linarith
  have hb_bd2 : ∀ (ω : Ω) (s : ℝ),
      ‖Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) s
        - (P {ω | V ω > s}).toReal‖ ≤ 2 := by
    intro ω s
    by_cases h : s ∈ Set.Iio (V ω)
    · rw [Set.indicator_of_mem h]
      calc ‖(1 : ℝ → ℝ) s - (P {ω | V ω > s}).toReal‖
          ≤ ‖(1 : ℝ → ℝ) s‖ + ‖(P {ω | V ω > s}).toReal‖ := norm_sub_le _ _
        _ ≤ 2 := by
          have e1 : ‖(1 : ℝ → ℝ) s‖ = 1 := by simp
          have e2 : ‖(P {ω | V ω > s}).toReal‖ ≤ 1 := by
            rw [Real.norm_eq_abs]
            have hle : (P {ω | V ω > s}).toReal ≤ 1 := by
              have hle' : P {ω | V ω > s} ≤ 1 := by
                calc P {ω | V ω > s} ≤ P Set.univ := measure_mono (Set.subset_univ _)
                  _ = 1 := measure_univ
              exact ENNReal.toReal_mono (by simp) hle'
            have nn : 0 ≤ (P {ω | V ω > s}).toReal := ENNReal.toReal_nonneg
            rw [abs_of_nonneg nn]
            exact hle
          rw [e1]
          linarith
    · rw [Set.indicator_of_notMem h]
      have hle : (P {ω | V ω > s}).toReal ≤ 1 := by
        have hle' : P {ω | V ω > s} ≤ 1 := by
          calc P {ω | V ω > s} ≤ P Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        exact ENNReal.toReal_mono (by simp) hle'
      simp only [zero_sub]
      calc ‖-(P {ω | V ω > s}).toReal‖ = |(P {ω | V ω > s}).toReal| := by
            rw [Real.norm_eq_abs, abs_neg]
        _ ≤ 2 := by
          have nn : 0 ≤ (P {ω | V ω > s}).toReal := ENNReal.toReal_nonneg
          rw [abs_of_nonneg nn]
          linarith
  have ha_joint : Measurable (fun q : Ω × ℝ =>
      Set.indicator (Set.Iio (U q.1)) (1 : ℝ → ℝ) q.2 - (P {ω | U ω > q.2}).toReal) :=
    hF_meas.sub (hPtail_meas.comp measurable_snd)
  have hb_joint : Measurable (fun q : Ω × ℝ =>
      Set.indicator (Set.Iio (V q.1)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal) :=
    hG_meas.sub (hQtail_meas.comp measurable_snd)
  -- Stage 15: H(ω,t,s) on Ω×(ℝ×ℝ); joint measurability + bound + integrability.
  -- Q2 is the square (vol|_Icc) × (vol|_Icc).
  have hH_meas : Measurable (fun p : Ω × (ℝ × ℝ) =>
      (Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2.1 - (P {ω | U ω > p.2.1}).toReal)
      * (Set.indicator (Set.Iio (V p.1)) (1 : ℝ → ℝ) p.2.2 - (P {ω | V ω > p.2.2}).toReal)) := by
    apply Measurable.mul
    · exact ha_joint.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    · exact hb_joint.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hH_bdd : ∀ p : Ω × (ℝ × ℝ),
      ‖(Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2.1 - (P {ω | U ω > p.2.1}).toReal)
        * (Set.indicator (Set.Iio (V p.1)) (1 : ℝ → ℝ) p.2.2 - (P {ω | V ω > p.2.2}).toReal)‖ ≤ 4 := by
    intro p
    rw [norm_mul]
    calc ‖Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2.1
          - (P {ω | U ω > p.2.1}).toReal‖
          * ‖Set.indicator (Set.Iio (V p.1)) (1 : ℝ → ℝ) p.2.2
          - (P {ω | V ω > p.2.2}).toReal‖
        ≤ 2 * 2 := mul_le_mul (ha_bd2 p.1 p.2.1) (hb_bd2 p.1 p.2.2)
          (by positivity) (by linarith)
      _ = 4 := by norm_num
  have hH_int : Integrable (fun p : Ω × (ℝ × ℝ) =>
      (Set.indicator (Set.Iio (U p.1)) (1 : ℝ → ℝ) p.2.1 - (P {ω | U ω > p.2.1}).toReal)
      * (Set.indicator (Set.Iio (V p.1)) (1 : ℝ → ℝ) p.2.2 - (P {ω | V ω > p.2.2}).toReal))
      (P.prod ((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M)))) :=
    Integrable.of_bound hH_meas.aestronglyMeasurable 4
      (by filter_upwards with p using hH_bdd p)
  -- Stage 16: swap; per-ω Q2 integral = A·B; inner = indicator cov.
  have hH_unc : Integrable
      (Function.uncurry fun ω (q : ℝ × ℝ) =>
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal))
      (P.prod ((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M)))) :=
    hH_int
  have hswap2 := integral_integral_swap hH_unc
  -- Stage 17: per-ω Q2 integral = A(ω)·B(ω) via integral_prod + hAB_int.
  have hperω : ∀ ω : Ω,
      (∫ q : ℝ × ℝ,
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal)
        ∂((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M))))
      = ((U ω + M) - (∫ ω', (U ω' + M) ∂P)) * ((V ω + M) - (∫ ω', (V ω' + M) ∂P)) := by
    intro ω
    have hmq : Measurable (fun q : ℝ × ℝ =>
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal)) := by
      apply Measurable.mul
      · exact ((Measurable.indicator measurable_const measurableSet_Iio).sub hPtail_meas).comp
          measurable_fst
      · exact ((Measurable.indicator measurable_const measurableSet_Iio).sub hQtail_meas).comp
          measurable_snd
    have hbq : ∀ q : ℝ × ℝ,
        ‖(Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
          * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal)‖ ≤ 4 := by
      intro q
      rw [norm_mul]
      calc ‖Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal‖
            * ‖Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal‖
          ≤ 2 * 2 := mul_le_mul (ha_bd2 ω q.1) (hb_bd2 ω q.2)
            (by positivity) (by linarith)
        _ = 4 := by norm_num
    have hint_q : Integrable (fun q : ℝ × ℝ =>
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal))
        ((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M))) :=
      Integrable.of_bound hmq.aestronglyMeasurable 4
        (by filter_upwards with q using hbq q)
    rw [integral_prod _ hint_q]
    exact (hAB_int ω).symm
  -- Stage 18: LHS of swap = cov(U+M,V+M); inner identification + bound.
  have hLHS2 : (∫ ω, ∫ q : ℝ × ℝ,
        (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal)
        ∂((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M))) ∂P)
      = cov[fun ω => U ω + M, fun ω => V ω + M; P] := by
    apply integral_congr_ae
    filter_upwards with ω
    exact hperω ω
  have hinner_eq : ∀ q : ℝ × ℝ,
      (∫ ω, (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal) ∂P)
      = (P ({ω | U ω > q.1} ∩ {ω | V ω > q.2})).toReal
        - (P {ω | U ω > q.1}).toReal * (P {ω | V ω > q.2}).toReal := by
    intro q
    have e1 : ∀ ω, Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1
        = Set.indicator {ω | U ω > q.1} (fun _ => (1 : ℝ)) ω := by
      intro ω
      by_cases h : U ω > q.1
      · have hm : q.1 ∈ Set.Iio (U ω) := Set.mem_Iio.2 h
        have h2 : ω ∈ {ω | U ω > q.1} := h
        simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
      · have hm : q.1 ∉ Set.Iio (U ω) := by
          simpa [Set.mem_Iio] using h
        have h2 : ω ∉ {ω | U ω > q.1} := h
        simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
    have e2 : ∀ ω, Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2
        = Set.indicator {ω | V ω > q.2} (fun _ => (1 : ℝ)) ω := by
      intro ω
      by_cases h : V ω > q.2
      · have hm : q.2 ∈ Set.Iio (V ω) := Set.mem_Iio.2 h
        have h2 : ω ∈ {ω | V ω > q.2} := h
        simp only [Set.indicator_of_mem hm, Set.indicator_of_mem h2, Pi.one_apply]
      · have hm : q.2 ∉ Set.Iio (V ω) := by
          simpa [Set.mem_Iio] using h
        have h2 : ω ∉ {ω | V ω > q.2} := h
        simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem h2]
    have eU : P[Set.indicator {ω | U ω > q.1} (fun _ => (1 : ℝ))]
        = (P {ω | U ω > q.1}).toReal := by
      rw [integral_indicator_const _ (hAt_amb q.1)]
      simp [Measure.real_def]
    have eV : P[Set.indicator {ω | V ω > q.2} (fun _ => (1 : ℝ))]
        = (P {ω | V ω > q.2}).toReal := by
      rw [integral_indicator_const _ (hBs_amb q.2)]
      simp [Measure.real_def]
    have hcov : cov[Set.indicator {ω | U ω > q.1} (fun _ => (1 : ℝ)),
        Set.indicator {ω | V ω > q.2} (fun _ => (1 : ℝ)); P]
        = (P ({ω | U ω > q.1} ∩ {ω | V ω > q.2})).toReal
          - (P {ω | U ω > q.1}).toReal * (P {ω | V ω > q.2}).toReal :=
      ProbabilityTheory.cov_indicator_eq P _ _ (hAt_amb q.1) (hBs_amb q.2)
    simp only [e1, e2]
    unfold ProbabilityTheory.covariance at hcov
    conv_lhs => rw [← eU, ← eV]
    exact hcov
  -- Stage 19: pointwise bound + area + constants-vanish + conclusion.
  have hinner_bd : ∀ q : ℝ × ℝ,
      ‖(∫ ω, (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
        * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal) ∂P)‖
        ≤ alphaMixingCoef P Y n := by
    intro q
    rw [Real.norm_eq_abs, hinner_eq q]
    exact hα_ts q.1 q.2
  -- cov(U+M,V+M) = ∫_Q2 inner by (hLHS2 via hperω) + swap.
  have hcovQ : cov[fun ω => U ω + M, fun ω => V ω + M; P]
      = ∫ q : ℝ × ℝ,
        (∫ ω, (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
          * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal) ∂P)
        ∂((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M))) := by
    have e1 : cov[fun ω => U ω + M, fun ω => V ω + M; P]
        = ∫ ω, (∫ q : ℝ × ℝ,
          (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
          * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal)
          ∂((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M)))) ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      exact (hperω ω).symm
    rw [e1]
    exact hswap2
  -- Stage 20: area bound + constants-vanish + conclusion.
  have hUint : Integrable U P := hU2.integrable (by norm_num)
  have hVint : Integrable V P := hV2.integrable (by norm_num)
  have hUV : cov[fun ω => U ω + M, fun ω => V ω + M; P] = cov[U, V; P] := by
    rw [covariance_add_const_left hUint M, covariance_add_const_right hVint M]
  have hvolQ2 : (((volume.restrict (Set.Icc (-M) M)).prod
      (volume.restrict (Set.Icc (-M) M))) Set.univ).toReal = 4 * M ^ 2 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod,
      Measure.restrict_apply_univ,
      Real.volume_Icc,
      ← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ M - -M),
      ENNReal.toReal_ofReal (mul_nonneg (by linarith : (0:ℝ) ≤ M - -M) (by linarith : (0:ℝ) ≤ M - -M))]
    ring
  have hfinal : ‖cov[fun ω => U ω + M, fun ω => V ω + M; P]‖ ≤ 4 * M ^ 2 * alphaMixingCoef P Y n := by
    have hle : ∀ᵐ q : ℝ × ℝ
        ∂((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M))),
        ‖(∫ ω, (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
          * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal) ∂P)‖
          ≤ alphaMixingCoef P Y n := by
      filter_upwards with q
      exact hinner_bd q
    calc ‖cov[fun ω => U ω + M, fun ω => V ω + M; P]‖
        = ‖∫ q : ℝ × ℝ,
          (∫ ω, (Set.indicator (Set.Iio (U ω)) (1 : ℝ → ℝ) q.1 - (P {ω | U ω > q.1}).toReal)
            * (Set.indicator (Set.Iio (V ω)) (1 : ℝ → ℝ) q.2 - (P {ω | V ω > q.2}).toReal) ∂P)
          ∂((volume.restrict (Set.Icc (-M) M)).prod (volume.restrict (Set.Icc (-M) M)))‖ := by
          rw [hcovQ]
      _ ≤ alphaMixingCoef P Y n
          * (((volume.restrict (Set.Icc (-M) M)).prod
            (volume.restrict (Set.Icc (-M) M))).real Set.univ) :=
        norm_integral_le_of_norm_le_const hle
      _ = 4 * M ^ 2 * alphaMixingCoef P Y n := by
        rw [Measure.real_def, hvolQ2]
        ring
  rw [Real.norm_eq_abs] at hfinal
  rw [← hUV]
  exact hfinal

