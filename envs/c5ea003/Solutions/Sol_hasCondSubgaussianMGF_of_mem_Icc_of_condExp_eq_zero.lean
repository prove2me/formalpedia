-- Prove2me | solution 1 for hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T23:45:32.800253+00:00
-- url     : https://prove2.me/submissions/0880101d-22d5-4cd0-bad3-70f1446433f5

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Kernel.Condexp
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : m ≤ mΩ) {X : Ω → ℝ} {a b : ℝ}
    (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hc : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) μ := by
  have hcomp : condExpKernel μ m ∘ₘ μ.trim hm = μ := condExpKernel_comp_trim hm
  refine Kernel.HasSubgaussianMGF.mk ?_ ?_
  · intro t
    rw [hcomp]
    exact integrable_exp_mul_of_mem_Icc hX.aemeasurable hb
  · have hb_comp : ∀ᵐ ω ∂(condExpKernel μ m ∘ₘ μ.trim hm), X ω ∈ Set.Icc a b := by
      rw [hcomp]; exact hb
    have hb_fib : ∀ᵐ ω' ∂(μ.trim hm),
        ∀ᵐ ω ∂(condExpKernel μ m ω'), X ω ∈ Set.Icc a b :=
      Measure.ae_ae_of_ae_comp hb_comp
    have hX_int : Integrable X μ := Integrable.of_mem_Icc a b hX.aemeasurable hb
    have hker : μ[X | m]
        =ᵐ[μ.trim hm] (fun ω' ↦ ∫ ω, X ω ∂(condExpKernel μ m ω')) :=
      condExp_ae_eq_trim_integral_condExpKernel hm hX_int
    have hc_trim : μ[X | m] =ᵐ[μ.trim hm] (0 : Ω → ℝ) := by
      have hsm : StronglyMeasurable[m] (μ[X | m]) := stronglyMeasurable_condExp
      exact (hsm.ae_eq_trim_of_stronglyMeasurable hm
        (stronglyMeasurable_const) hc)
    have hcent : (fun ω' ↦ ∫ ω, X ω ∂(condExpKernel μ m ω')) =ᵐ[μ.trim hm] 0 :=
      hker.symm.trans hc_trim
    filter_upwards [hb_fib, hcent] with ω' hb_ω' hcent_ω'
    intro t
    have hmgf := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (μ := condExpKernel μ m ω') hX.aemeasurable hb_ω' hcent_ω'
    exact hmgf.mgf_le t
