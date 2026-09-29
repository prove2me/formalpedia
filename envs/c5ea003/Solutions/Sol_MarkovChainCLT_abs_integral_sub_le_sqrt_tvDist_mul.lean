-- Prove2me | solution 1 for MarkovChainCLT.abs_integral_sub_le_sqrt_tvDist_mul
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T22:49:52.171396+00:00
-- url     : https://prove2.me/submissions/de7e587d-27b6-447d-a95c-ebb0b4d1be65

import Definitions.Def_TotalVariationDist
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open MarkovChainCLT
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

theorem solution {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : X → ℝ) (hh : Measurable h)
    (hμ : Integrable (fun x => (h x) ^ 2) μ) (hν : Integrable (fun x => (h x) ^ 2) ν) :
    |∫ x, h x ∂μ - ∫ x, h x ∂ν|
      ≤ Real.sqrt (tvDist μ ν) *
        (Real.sqrt (∫ x, (h x) ^ 2 ∂μ) + Real.sqrt (∫ x, (h x) ^ 2 ∂ν)) := by
  classical
  -- Cauchy-Schwarz against an arbitrary finite measure
  have cs : ∀ (ρ : Measure X), IsFiniteMeasure ρ → Integrable (fun x => (h x) ^ 2) ρ →
      |∫ x, h x ∂ρ| ≤ Real.sqrt ((ρ Set.univ).toReal) * Real.sqrt (∫ x, (h x) ^ 2 ∂ρ) := by
    intro ρ hfin hsq
    have hint : Integrable h ρ := by
      refine Integrable.mono' (g := fun x => (1 + (h x) ^ 2) / 2)
        ((integrable_const (1 : ℝ)).add hsq |>.div_const 2) hh.aestronglyMeasurable ?_
      refine ae_of_all _ (fun x => ?_)
      rw [Real.norm_eq_abs]
      nlinarith [sq_nonneg (|h x| - 1), abs_nonneg (h x), sq_abs (h x)]
    have habs : Integrable (fun x => |h x|) ρ := hint.abs
    set m : ℝ := (ρ Set.univ).toReal with hm
    set Q : ℝ := ∫ x, (h x) ^ 2 ∂ρ with hQ
    set I : ℝ := ∫ x, |h x| ∂ρ with hI
    have hQ0 : 0 ≤ Q := integral_nonneg (fun x => sq_nonneg _)
    have hI0 : 0 ≤ I := integral_nonneg (fun x => abs_nonneg _)
    have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
    have habsint : |∫ x, h x ∂ρ| ≤ I := abs_integral_le_integral_abs
    rcases eq_or_lt_of_le hm0 with hmz | hmpos
    · -- degenerate: the measure is zero
      have hzero : ρ Set.univ = 0 := by
        have := (ENNReal.toReal_eq_zero_iff (ρ Set.univ)).mp hmz.symm
        rcases this with h1 | h1
        · exact h1
        · exact absurd h1 (measure_ne_top ρ Set.univ)
      have hρ0 : ρ = 0 := by
        ext s hs
        exact le_antisymm (le_trans (measure_mono (Set.subset_univ s)) (le_of_eq hzero))
          (by simp)
      rw [hρ0]
      simp only [integral_zero_measure, abs_zero]
      positivity
    · -- the Cauchy-Schwarz discriminant argument
      set lam : ℝ := I / m with hlam
      have hexp : ∫ x, (|h x| - lam) ^ 2 ∂ρ = Q - 2 * lam * I + lam ^ 2 * m := by
        have hev : ∀ x, (|h x| - lam) ^ 2
            = (h x) ^ 2 - 2 * lam * |h x| + lam ^ 2 := by
          intro x
          have : |h x| ^ 2 = (h x) ^ 2 := sq_abs _
          nlinarith [this]
        rw [integral_congr_ae (ae_of_all _ hev)]
        have i2 : Integrable (fun x => 2 * lam * |h x|) ρ := habs.const_mul (2 * lam)
        have i1 : Integrable (fun x => (h x) ^ 2 - 2 * lam * |h x|) ρ := hsq.sub i2
        rw [integral_add i1 (integrable_const (lam ^ 2)), integral_sub hsq i2,
          integral_const_mul, integral_const]
        simp [Measure.real, hm, hQ, hI]
        ring
      have hnn : 0 ≤ ∫ x, (|h x| - lam) ^ 2 ∂ρ := integral_nonneg (fun x => sq_nonneg _)
      rw [hexp] at hnn
      have hkey : I ^ 2 ≤ m * Q := by
        have hmne : m ≠ 0 := ne_of_gt hmpos
        rw [hlam] at hnn
        field_simp at hnn
        nlinarith [hnn]
      calc |∫ x, h x ∂ρ| ≤ I := habsint
        _ = Real.sqrt (I ^ 2) := by rw [Real.sqrt_sq hI0]
        _ ≤ Real.sqrt (m * Q) := Real.sqrt_le_sqrt hkey
        _ = Real.sqrt m * Real.sqrt Q := Real.sqrt_mul hm0 Q
  -- the total variation distance bounds every set difference
  have hbdd : BddAbove {r : ℝ | ∃ A : Set X, MeasurableSet A ∧
      r = |(μ A).toReal - (ν A).toReal|} := by
    refine ⟨1, ?_⟩
    rintro r ⟨B, hB, rfl⟩
    have h1 : (μ B).toReal ≤ 1 := by
      have := ENNReal.toReal_mono (by simp) (prob_le_one (μ := μ) (s := B))
      simpa using this
    have h2 : (ν B).toReal ≤ 1 := by
      have := ENNReal.toReal_mono (by simp) (prob_le_one (μ := ν) (s := B))
      simpa using this
    have h3 : (0 : ℝ) ≤ (μ B).toReal := ENNReal.toReal_nonneg
    have h4 : (0 : ℝ) ≤ (ν B).toReal := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  have htvle : ∀ B : Set X, MeasurableSet B →
      |(μ B).toReal - (ν B).toReal| ≤ tvDist μ ν := by
    intro B hB
    exact le_csSup hbdd ⟨B, hB, rfl⟩
  have htv0 : 0 ≤ tvDist μ ν := by
    have := htvle Set.univ MeasurableSet.univ
    exact le_trans (abs_nonneg _) this
  -- Hahn decomposition
  obtain ⟨A, hAm, hA1, hA2⟩ := hahn_decomposition μ ν
  have hle1 : ν.restrict A ≤ μ.restrict A := by
    refine Measure.le_iff.mpr (fun s hs => ?_)
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hA1 _ (hs.inter hAm) Set.inter_subset_right
  have hle2 : μ.restrict Aᶜ ≤ ν.restrict Aᶜ := by
    refine Measure.le_iff.mpr (fun s hs => ?_)
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hA2 _ (hs.inter hAm.compl) Set.inter_subset_right
  set ρ₁ : Measure X := μ.restrict A - ν.restrict A with hρ₁
  set ρ₂ : Measure X := ν.restrict Aᶜ - μ.restrict Aᶜ with hρ₂
  have hsum1 : ρ₁ + ν.restrict A = μ.restrict A := Measure.sub_add_cancel_of_le hle1
  have hsum2 : ρ₂ + μ.restrict Aᶜ = ν.restrict Aᶜ := Measure.sub_add_cancel_of_le hle2
  have hρ₁le : ρ₁ ≤ μ := le_trans Measure.sub_le Measure.restrict_le_self
  have hρ₂le : ρ₂ ≤ ν := le_trans Measure.sub_le Measure.restrict_le_self
  haveI : IsFiniteMeasure ρ₁ := isFiniteMeasure_of_le μ hρ₁le
  haveI : IsFiniteMeasure ρ₂ := isFiniteMeasure_of_le ν hρ₂le
  -- integrability transfers along `≤`
  have hintμ : Integrable h μ := by
    refine Integrable.mono' (g := fun x => (1 + (h x) ^ 2) / 2)
      ((integrable_const (1 : ℝ)).add hμ |>.div_const 2) hh.aestronglyMeasurable ?_
    refine ae_of_all _ (fun x => ?_)
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|h x| - 1), abs_nonneg (h x), sq_abs (h x)]
  have hintν : Integrable h ν := by
    refine Integrable.mono' (g := fun x => (1 + (h x) ^ 2) / 2)
      ((integrable_const (1 : ℝ)).add hν |>.div_const 2) hh.aestronglyMeasurable ?_
    refine ae_of_all _ (fun x => ?_)
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|h x| - 1), abs_nonneg (h x), sq_abs (h x)]
  have hsqρ₁ : Integrable (fun x => (h x) ^ 2) ρ₁ := hμ.mono_measure hρ₁le
  have hsqρ₂ : Integrable (fun x => (h x) ^ 2) ρ₂ := hν.mono_measure hρ₂le
  have hintρ₁ : Integrable h ρ₁ := hintμ.mono_measure hρ₁le
  have hintρ₂ : Integrable h ρ₂ := hintν.mono_measure hρ₂le
  have hintνA : Integrable h (ν.restrict A) := hintν.restrict
  have hintμAc : Integrable h (μ.restrict Aᶜ) := hintμ.restrict
  -- the difference of integrals is a difference of two positive parts
  have hsplit : (∫ x, h x ∂μ) - ∫ x, h x ∂ν = (∫ x, h x ∂ρ₁) - ∫ x, h x ∂ρ₂ := by
    have e1 : ∫ x, h x ∂(μ.restrict A) = (∫ x, h x ∂ρ₁) + ∫ x, h x ∂(ν.restrict A) := by
      rw [← hsum1, integral_add_measure hintρ₁ hintνA]
    have e2 : ∫ x, h x ∂(ν.restrict Aᶜ) = (∫ x, h x ∂ρ₂) + ∫ x, h x ∂(μ.restrict Aᶜ) := by
      rw [← hsum2, integral_add_measure hintρ₂ hintμAc]
    have e3 : (∫ x, h x ∂(μ.restrict A)) + ∫ x, h x ∂(μ.restrict Aᶜ) = ∫ x, h x ∂μ :=
      integral_add_compl hAm hintμ
    have e4 : (∫ x, h x ∂(ν.restrict A)) + ∫ x, h x ∂(ν.restrict Aᶜ) = ∫ x, h x ∂ν :=
      integral_add_compl hAm hintν
    rw [← e3, ← e4, e1, e2]
    ring
  -- masses are bounded by the total variation distance
  have hmass1 : (ρ₁ Set.univ).toReal ≤ tvDist μ ν := by
    have hle : ν A ≤ μ A := hA1 A hAm (subset_refl A)
    have happ : ρ₁ Set.univ = μ A - ν A := by
      rw [hρ₁, Measure.sub_apply MeasurableSet.univ hle1,
        Measure.restrict_apply MeasurableSet.univ, Measure.restrict_apply MeasurableSet.univ]
      simp
    rw [happ, ENNReal.toReal_sub_of_le hle (measure_ne_top μ A)]
    refine le_trans (le_abs_self _) (htvle A hAm)
  have hmass2 : (ρ₂ Set.univ).toReal ≤ tvDist μ ν := by
    have hle : μ Aᶜ ≤ ν Aᶜ := hA2 Aᶜ hAm.compl (subset_refl Aᶜ)
    have happ : ρ₂ Set.univ = ν Aᶜ - μ Aᶜ := by
      rw [hρ₂, Measure.sub_apply MeasurableSet.univ hle2,
        Measure.restrict_apply MeasurableSet.univ, Measure.restrict_apply MeasurableSet.univ]
      simp
    rw [happ, ENNReal.toReal_sub_of_le hle (measure_ne_top ν Aᶜ)]
    refine le_trans ?_ (htvle Aᶜ hAm.compl)
    rw [abs_sub_comm]
    exact le_abs_self _
  -- second moments only decrease
  have hsm1 : (∫ x, (h x) ^ 2 ∂ρ₁) ≤ ∫ x, (h x) ^ 2 ∂μ :=
    integral_mono_measure hρ₁le (ae_of_all _ (fun x => sq_nonneg _)) hμ
  have hsm2 : (∫ x, (h x) ^ 2 ∂ρ₂) ≤ ∫ x, (h x) ^ 2 ∂ν :=
    integral_mono_measure hρ₂le (ae_of_all _ (fun x => sq_nonneg _)) hν
  -- assemble
  have hb1 : |∫ x, h x ∂ρ₁| ≤ Real.sqrt (tvDist μ ν) * Real.sqrt (∫ x, (h x) ^ 2 ∂μ) := by
    refine le_trans (cs ρ₁ inferInstance hsqρ₁) ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hmass1) (Real.sqrt_le_sqrt hsm1)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hb2 : |∫ x, h x ∂ρ₂| ≤ Real.sqrt (tvDist μ ν) * Real.sqrt (∫ x, (h x) ^ 2 ∂ν) := by
    refine le_trans (cs ρ₂ inferInstance hsqρ₂) ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hmass2) (Real.sqrt_le_sqrt hsm2)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [hsplit]
  calc |(∫ x, h x ∂ρ₁) - ∫ x, h x ∂ρ₂| ≤ |∫ x, h x ∂ρ₁| + |∫ x, h x ∂ρ₂| := abs_sub _ _
    _ ≤ Real.sqrt (tvDist μ ν) * Real.sqrt (∫ x, (h x) ^ 2 ∂μ)
        + Real.sqrt (tvDist μ ν) * Real.sqrt (∫ x, (h x) ^ 2 ∂ν) := by linarith
    _ = Real.sqrt (tvDist μ ν) *
        (Real.sqrt (∫ x, (h x) ^ 2 ∂μ) + Real.sqrt (∫ x, (h x) ^ 2 ∂ν)) := by ring
