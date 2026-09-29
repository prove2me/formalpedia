-- Prove2me | solution 1 for DonskerVaradhan.integral_sub_klDiv_le_log_integral_exp
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T02:56:06.067934+00:00
-- url     : https://prove2.me/submissions/3281a6e7-7b4f-4cda-9185-37106a50b6c0

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Tilted

open Real MeasureTheory Set
open scoped ENNReal NNReal

set_option autoImplicit false

theorem solution {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
    {Q : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (hQμ : Q ≪ μ)
    (hf : Integrable (fun x ↦ exp (f x)) μ)
    (hf_int : Integrable f Q)
    (h_llr : Integrable (llr Q μ) Q) :
    ∫ x, f x ∂Q - (InformationTheory.klDiv Q μ).toReal ≤ log (∫ x, exp (f x) ∂μ) := by
  haveI : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted hf
  have hμtil : μ ≪ μ.tilted f := absolutelyContinuous_tilted hf
  have hQtil : Q ≪ μ.tilted f := hQμ.trans hμtil
  have hllr : (fun x ↦ llr Q (μ.tilted f) x)
      =ᵐ[Q] fun x ↦ -f x + log (∫ z, exp (f z) ∂μ) + llr Q μ x :=
    llr_tilted_right hQμ hf
  have hint1 : Integrable (fun x ↦ -f x + log (∫ z, exp (f z) ∂μ)) Q :=
    hf_int.neg.add (integrable_const _)
  have hkl : (InformationTheory.klDiv Q (μ.tilted f)).toReal = ∫ x, llr Q (μ.tilted f) x ∂Q :=
    InformationTheory.toReal_klDiv_of_measure_eq hQtil (by rw [measure_univ, measure_univ])
  have hklμ : (InformationTheory.klDiv Q μ).toReal = ∫ x, llr Q μ x ∂Q :=
    InformationTheory.toReal_klDiv_of_measure_eq hQμ (by rw [measure_univ, measure_univ])
  have hexp : ∫ x, llr Q (μ.tilted f) x ∂Q
      = -(∫ x, f x ∂Q) + log (∫ z, exp (f z) ∂μ) + ∫ x, llr Q μ x ∂Q := by
    rw [integral_congr_ae hllr]
    rw [integral_add hint1 h_llr]
    have hadd : ∫ a, ((fun x ↦ -f x) a + (fun _ ↦ log (∫ z, exp (f z) ∂μ)) a) ∂Q
        = ∫ a, (fun x ↦ -f x) a ∂Q + ∫ a, (fun _ ↦ log (∫ z, exp (f z) ∂μ)) a ∂Q :=
      integral_add hf_int.neg (integrable_const _)
    have hh : ∫ a, -f a + log (∫ z, exp (f z) ∂μ) ∂Q
        = -(∫ x, f x ∂Q) + log (∫ z, exp (f z) ∂μ) := by
      rw [hadd, integral_neg]; simp
    rw [hh]
  have hgibbs : (0 : ℝ) ≤ (InformationTheory.klDiv Q (μ.tilted f)).toReal :=
    ENNReal.toReal_nonneg
  rw [hkl, hexp] at hgibbs
  rw [hklμ]
  linarith
