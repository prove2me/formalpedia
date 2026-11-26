-- Prove2me | solution 1 for ReweightedNPMLE.integral_abs_le_sqrt_weightedL2
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:03:51.132982+00:00
-- url     : https://prove2.me/submissions/eb75fa33-a70c-4e1f-b2bd-b77be6af562b

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

/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Weighted Cauchy--Schwarz in the exact form used by the Gaussian-mixture
net argument.  A positive reference density converts weighted `L²` error
into ordinary `L¹` error. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h φ : Ω → ℝ)
    (hh : AEStronglyMeasurable h μ) (hφm : AEStronglyMeasurable φ μ)
    (hφpos : ∀ᵐ x ∂μ, 0 < φ x)
    (hweighted : Integrable (fun x ↦ h x ^ 2 / φ x) μ)
    (hφint : Integrable φ μ) :
    ∫ x, |h x| ∂μ ≤
      (∫ x, h x ^ 2 / φ x ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, φ x ∂μ) ^ (1 / 2 : ℝ) := by
  let f : Ω → ℝ := fun x ↦ |h x| / Real.sqrt (φ x)
  let g : Ω → ℝ := fun x ↦ Real.sqrt (φ x)
  have hgmeas : AEStronglyMeasurable g μ := by
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hφm
  have hfmeas : AEStronglyMeasurable f μ := by
    exact (hh.norm.aemeasurable.div hgmeas.aemeasurable).aestronglyMeasurable
  have hf_sq : Integrable (fun x ↦ f x ^ 2) μ := by
    apply hweighted.congr
    filter_upwards [hφpos] with x hx
    dsimp [f]
    rw [div_pow, sq_abs, Real.sq_sqrt hx.le]
  have hg_sq : Integrable (fun x ↦ g x ^ 2) μ := by
    apply hφint.congr
    filter_upwards [hφpos] with x hx
    dsimp [g]
    exact (Real.sq_sqrt hx.le).symm
  have hf : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfmeas).2 hf_sq
  have hg : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgmeas).2 hg_sq
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) Real.HolderConjugate.two_two
    (f := f) (g := g)
    (Filter.Eventually.of_forall fun x ↦
      div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    (Filter.Eventually.of_forall fun x ↦ Real.sqrt_nonneg _) hf' hg'
  calc
    (∫ x, |h x| ∂μ) = ∫ x, f x * g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hφpos] with x hx
      dsimp [f, g]
      field_simp [Real.sqrt_ne_zero'.2 hx]
    _ ≤ (∫ x, f x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hholder
    _ = (∫ x, h x ^ 2 / φ x ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, φ x ∂μ) ^ (1 / 2 : ℝ) := by
      congr 2
      · apply integral_congr_ae
        filter_upwards [hφpos] with x hx
        dsimp [f]
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
        rw [div_pow, sq_abs, Real.sq_sqrt hx.le]
      · apply integral_congr_ae
        filter_upwards [hφpos] with x hx
        dsimp [g]
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
        exact Real.sq_sqrt hx.le
