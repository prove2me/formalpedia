-- Prove2me | solution 1 for MarkovChainCLT.abs_integral_sub_le_tvDist
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T20:48:35.537988+00:00
-- url     : https://prove2.me/submissions/5fea9fe9-23c5-435a-8a2d-e49690724012

import Definitions.Def_TotalVariationDist
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open MarkovChainCLT

set_option maxHeartbeats 1000000

theorem solution {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X → ℝ) (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ tvDist μ ν := by
  obtain ⟨s, hs, hle_s, hle_sc⟩ := hahn_decomposition μ ν
  have hint : ∀ (ρ : Measure X), IsFiniteMeasure ρ → Integrable f ρ := by
    intro ρ hρ
    haveI := hρ
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const (1:ℝ)).mono ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h0 x), abs_one]
    exact h1 x
  -- the general one-sided bound
  have key : ∀ (ρ σ : Measure X), IsFiniteMeasure ρ → IsFiniteMeasure σ →
      ∀ b : Set X, MeasurableSet b → σ.restrict b ≤ ρ.restrict b →
        ρ.restrict bᶜ ≤ σ.restrict bᶜ →
      (∫ x, f x ∂ρ) - (∫ x, f x ∂σ) ≤ (ρ b).toReal - (σ b).toReal := by
    intro ρ σ hρ hσ b hbm hb hbc
    haveI := hρ; haveI := hσ
    have hIρ := hint ρ hρ
    have hIσ := hint σ hσ
    have h1a : (∫ x in bᶜ, f x ∂ρ) ≤ ∫ x in bᶜ, f x ∂σ :=
      integral_mono_measure hbc (Filter.Eventually.of_forall h0) hIσ.restrict
    have h2b : (∫ x in b, (1 - f x) ∂σ) ≤ ∫ x in b, (1 - f x) ∂ρ := by
      refine integral_mono_measure hb (Filter.Eventually.of_forall (fun x => by
        simp only [Pi.zero_apply]; linarith [h1 x])) ?_
      exact ((integrable_const (1:ℝ)).sub hIρ).restrict
    rw [integral_sub (integrable_const _).restrict hIσ.restrict,
      integral_sub (integrable_const _).restrict hIρ.restrict] at h2b
    simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
      Measure.restrict_apply_univ] at h2b
    have hsplitρ : (∫ x in b, f x ∂ρ) + (∫ x in bᶜ, f x ∂ρ) = ∫ x, f x ∂ρ :=
      integral_add_compl hbm hIρ
    have hsplitσ : (∫ x in b, f x ∂σ) + (∫ x in bᶜ, f x ∂σ) = ∫ x, f x ∂σ :=
      integral_add_compl hbm hIσ
    linarith
  -- every set difference is bounded by the total variation distance
  have hbnd : ∀ (b : Set X), MeasurableSet b →
      |(μ b).toReal - (ν b).toReal| ≤ tvDist μ ν := by
    intro b hb
    have hmem : |(μ b).toReal - (ν b).toReal|
        ∈ {r | ∃ A : Set X, MeasurableSet A ∧ r = |(μ A).toReal - (ν A).toReal|} :=
      ⟨b, hb, rfl⟩
    have hbdd : BddAbove {r | ∃ A : Set X, MeasurableSet A ∧ r = |(μ A).toReal - (ν A).toReal|} := by
      refine ⟨(μ Set.univ).toReal + (ν Set.univ).toReal, ?_⟩
      rintro r ⟨A, hA, rfl⟩
      have hμA : (μ A).toReal ≤ (μ Set.univ).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
      have hνA : (ν A).toReal ≤ (ν Set.univ).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
      have hn1 : (0:ℝ) ≤ (μ A).toReal := ENNReal.toReal_nonneg
      have hn2 : (0:ℝ) ≤ (ν A).toReal := ENNReal.toReal_nonneg
      have hu1 : (0:ℝ) ≤ (μ Set.univ).toReal := ENNReal.toReal_nonneg
      have hu2 : (0:ℝ) ≤ (ν Set.univ).toReal := ENNReal.toReal_nonneg
      rw [abs_le]
      constructor <;> linarith
    exact le_csSup hbdd hmem
  have hres_s : ν.restrict s ≤ μ.restrict s := by
    refine Measure.le_iff.mpr (fun t ht => ?_)
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hle_s _ (ht.inter hs) Set.inter_subset_right
  have hres_sc : μ.restrict sᶜ ≤ ν.restrict sᶜ := by
    refine Measure.le_iff.mpr (fun t ht => ?_)
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hle_sc _ (ht.inter hs.compl) Set.inter_subset_right
  rw [abs_le]
  constructor
  · have hk := key ν μ ‹_› ‹_› sᶜ hs.compl hres_sc (by rwa [compl_compl])
    have hb := hbnd sᶜ hs.compl
    rw [abs_le] at hb
    linarith [hb.1, hb.2]
  · have hk := key μ ν ‹_› ‹_› s hs hres_s hres_sc
    have hb := hbnd s hs
    rw [abs_le] at hb
    linarith [hb.1, hb.2]
