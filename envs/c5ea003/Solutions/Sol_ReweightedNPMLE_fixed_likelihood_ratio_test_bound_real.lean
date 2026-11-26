-- Prove2me | solution 1 for ReweightedNPMLE.fixed_likelihood_ratio_test_bound_real
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:05:20.079106+00:00
-- url     : https://prove2.me/submissions/cf4b56dc-21a9-46e8-9714-1d27f8112f1b

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Hellinger

/-!
# Finite-net likelihood testing

This file isolates the probability-theoretic union-bound step in the proof of
the paper's uniform near-MLE theorem.  The analytic construction of a
Gaussian-mixture net and the fixed-density likelihood-ratio estimate enter as
explicit hypotheses; the passage from those pointwise estimates to one event
which controls every candidate is proved here.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
/--
The fixed-density likelihood-ratio test in real-valued probability form.
The expectation premise is exactly the square-root likelihood-ratio identity
followed by `affinity_pow_le_exp_neg`.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (logLR : Ω → ℝ) (n : ℕ) (h : ℝ)
    (hint : Integrable (fun ω ↦ Real.exp (logLR ω / 2)) μ)
    (hexpect : ∫ ω, Real.exp (logLR ω / 2) ∂μ ≤
      Real.exp (-(n : ℝ) * h / 2)) :
    μ.real {ω | -2 ≤ logLR ω} ≤ Real.exp (1 - (n : ℝ) * h / 2) := by
  have hset : {ω | Real.exp (-1) ≤ Real.exp (logLR ω / 2)} =
      {ω | -2 ≤ logLR ω} := by
    ext ω
    simp only [mem_setOf_eq]
    rw [Real.exp_le_exp]
    constructor <;> intro hω <;> linarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω ↦ Real.exp (logLR ω / 2))
    (Filter.Eventually.of_forall fun ω ↦ (Real.exp_pos _).le) hint (Real.exp (-1))
  rw [hset] at hmarkov
  have hprod : Real.exp (-1) * μ.real {ω | -2 ≤ logLR ω} ≤
      Real.exp (-(n : ℝ) * h / 2) := hmarkov.trans hexpect
  calc
    μ.real {ω | -2 ≤ logLR ω} =
        Real.exp 1 * (Real.exp (-1) * μ.real {ω | -2 ≤ logLR ω}) := by
          rw [← mul_assoc, ← Real.exp_add]
          norm_num
    _ ≤ Real.exp 1 * Real.exp (-(n : ℝ) * h / 2) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (1 - (n : ℝ) * h / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
