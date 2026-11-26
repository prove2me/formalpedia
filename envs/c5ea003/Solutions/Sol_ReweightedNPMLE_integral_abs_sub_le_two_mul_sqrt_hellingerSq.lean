-- Prove2me | solution 1 for ReweightedNPMLE.integral_abs_sub_le_two_mul_sqrt_hellingerSq
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:12:08.170292+00:00
-- url     : https://prove2.me/submissions/be8a8a5b-0295-435f-a67f-af105bdf8dca

import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Hellinger

-- Inline helpers preserved from ReweightedNPMLE.Hellinger.
section
/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

namespace ReweightedNPMLE

















/-- Integrable nonnegative densities have an integrable squared Hellinger
integrand.  This discharges a recurring analytic side condition for finite
Gaussian mixtures. -/
theorem hellingerIntegrand_integrable_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p q : Ω → ℝ)
    (hpmeas : AEStronglyMeasurable p μ) (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ) :
    Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
  have hmeas : AEStronglyMeasurable
      (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
    exact ((Real.continuous_sqrt.comp_aestronglyMeasurable hpmeas).sub
      (Real.continuous_sqrt.comp_aestronglyMeasurable hqmeas)).pow 2
  apply ((hpint.add hqint).const_mul 2).mono' hmeas
  filter_upwards [hp, hq] with x hpx hqx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ≤ 2 * (p x + q x)
  nlinarith [sq_nonneg (Real.sqrt (p x) + Real.sqrt (q x)),
    Real.sq_sqrt hpx, Real.sq_sqrt hqx]







































end ReweightedNPMLE
end

/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Total-variation (`L¹`) error is controlled by squared Hellinger distance.
For probability densities in the manuscript's normalization,
`∫ |p - q| ≤ 2 √(H²(p,q))`. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hpmeas : AEStronglyMeasurable p μ) (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (hpone : ∫ x, p x ∂μ = 1) (hqone : ∫ x, q x ∂μ = 1) :
    ∫ x, |p x - q x| ∂μ ≤ 2 * Real.sqrt (hellingerSq μ p q) := by
  let f : Ω → ℝ := fun x ↦ |Real.sqrt (p x) - Real.sqrt (q x)|
  let g : Ω → ℝ := fun x ↦ Real.sqrt (p x) + Real.sqrt (q x)
  have hfmeas : AEStronglyMeasurable f μ := by
    exact (((Real.continuous_sqrt.comp_aestronglyMeasurable hpmeas).sub
      (Real.continuous_sqrt.comp_aestronglyMeasurable hqmeas)).norm)
  have hgmeas : AEStronglyMeasurable g μ := by
    exact (Real.continuous_sqrt.comp_aestronglyMeasurable hpmeas).add
      (Real.continuous_sqrt.comp_aestronglyMeasurable hqmeas)
  have hhell := hellingerIntegrand_integrable_of_integrable
    μ p q hpmeas hqmeas hp hq hpint hqint
  have hfsq : Integrable (fun x ↦ f x ^ 2) μ := by
    apply hhell.congr
    exact Filter.Eventually.of_forall fun x ↦ by
      simp only [f, sq_abs]
  have hgsq : Integrable (fun x ↦ g x ^ 2) μ := by
    apply ((hpint.add hqint).const_mul 2).mono' (hgmeas.pow 2)
    filter_upwards [hp, hq] with x hpx hqx
    change ‖g x ^ 2‖ ≤ 2 * (p x + q x)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    dsimp [g]
    nlinarith [Real.sq_sqrt hpx, Real.sq_sqrt hqx,
      sq_nonneg (Real.sqrt (p x) - Real.sqrt (q x))]
  have hf : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfmeas).2 hfsq
  have hg : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgmeas).2 hgsq
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) Real.HolderConjugate.two_two
    (f := f) (g := g)
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg _)
    (Filter.Eventually.of_forall fun x ↦
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hf' hg'
  have hholder' :
      ∫ x, f x * g x ∂μ ≤
        Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
    norm_num [Real.sqrt_eq_rpow] at hholder ⊢
    exact hholder
  have hgfour : ∫ x, g x ^ 2 ∂μ ≤ 4 := by
    calc
      (∫ x, g x ^ 2 ∂μ) ≤ ∫ x, 2 * (p x + q x) ∂μ := by
        apply integral_mono_ae hgsq ((hpint.add hqint).const_mul 2)
        filter_upwards [hp, hq] with x hpx hqx
        dsimp [g]
        nlinarith [Real.sq_sqrt hpx, Real.sq_sqrt hqx,
          sq_nonneg (Real.sqrt (p x) - Real.sqrt (q x))]
      _ = 4 := by
        rw [integral_const_mul, integral_add hpint hqint, hpone, hqone]
        norm_num
  have hgroot : Real.sqrt (∫ x, g x ^ 2 ∂μ) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have hprod :
      (∫ x, |p x - q x| ∂μ) = ∫ x, f x * g x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hp, hq] with x hpx hqx
    dsimp [f, g]
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
      ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt hpx, Real.sq_sqrt hqx]
  have hfhell : (∫ x, f x ^ 2 ∂μ) = hellingerSq μ p q := by
    unfold hellingerSq
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by simp only [f, sq_abs]
  calc
    (∫ x, |p x - q x| ∂μ) = ∫ x, f x * g x ∂μ := hprod
    _ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := hholder'
    _ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * 2 :=
      mul_le_mul_of_nonneg_left hgroot (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (hellingerSq μ p q) := by rw [hfhell]; ring
