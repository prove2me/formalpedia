-- Prove2me | solution 1 for DonskerVaradhan.klDiv_tilted_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T02:56:05.800524+00:00
-- url     : https://prove2.me/submissions/8f73e92f-cb27-4fef-8fcd-6c9000741414

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Tilted

open Real MeasureTheory Set
open scoped ENNReal NNReal

set_option autoImplicit false

theorem solution {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
    [IsProbabilityMeasure μ]
    (hf : Integrable (fun x ↦ exp (f x)) μ)
    (hf_int : Integrable f (μ.tilted f)) :
    (InformationTheory.klDiv (μ.tilted f) μ).toReal
      = ∫ x, f x ∂(μ.tilted f) - log (∫ x, exp (f x) ∂μ) := by
  haveI : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted hf
  have hac : μ.tilted f ≪ μ := tilted_absolutelyContinuous μ f
  have hmass : (μ.tilted f) univ = μ univ := by rw [measure_univ, measure_univ]
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac hmass]
  have hllr : (fun x ↦ llr (μ.tilted f) μ x)
      =ᵐ[μ.tilted f] fun x ↦ f x - log (∫ x, exp (f x) ∂μ) := by
    have hμ : (fun x ↦ log ((μ.tilted f).rnDeriv μ x).toReal)
        =ᵐ[μ] fun x ↦ f x - log (∫ x, exp (f x) ∂μ) :=
      log_rnDeriv_tilted_left_self hf
    exact hac.ae_le hμ
  rw [integral_congr_ae hllr]
  rw [integral_sub hf_int (integrable_const _)]
  simp
