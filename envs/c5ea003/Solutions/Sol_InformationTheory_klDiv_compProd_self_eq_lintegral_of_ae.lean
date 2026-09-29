-- Prove2me | solution 1 for InformationTheory.klDiv_compProd_self_eq_lintegral_of_ae
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T17:01:14.508692+00:00
-- url     : https://prove2.me/submissions/1721f937-9e9f-4a87-bcb0-dc1bf9e2ae58

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# The conditional term of the chain rule, as an integral

`klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ`, assuming fibrewise absolute
continuity only almost everywhere.

Mathlib's chain rule `klDiv_compProd_eq_add` leaves the conditional divergence in the form
`klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`; this evaluates it as the average of the fibrewise divergences,
which is the form in which conditional relative entropy is normally used and stated.

L&S Exercise 14.12 (chain rule, printed p. 196) writes the decomposition in exactly this form:
`D(P, Q) = ∑_t E_P[D(P_t(·|X_1..X_{t-1}), Q_t(·|X_1..X_{t-1}))]`.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

theorem solution {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel α β)
    [IsFiniteKernel κ] [IsFiniteKernel η] (hac : ∀ᵐ a ∂μ, κ a ≪ η a) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  classical
  -- the fibrewise density, as a jointly measurable function
  set f : α → β → ℝ≥0∞ := κ.rnDeriv η with hf
  have hf_meas : Measurable (Function.uncurry f) := κ.measurable_rnDeriv η
  have hκ : (η.withDensity f) =ᵐ[μ] κ := by
    filter_upwards [hac] with a ha
    ext s hs
    rw [hf, Kernel.withDensity_rnDeriv_eq ha]
  -- absolute continuity of the composition-products
  have hac' : μ ⊗ₘ κ ≪ μ ⊗ₘ η := Measure.AbsolutelyContinuous.compProd_right hac
  -- the density of the composition-products is the fibrewise one
  have hwd : (μ ⊗ₘ η).withDensity (fun p ↦ f p.1 p.2) = μ ⊗ₘ κ := by
    rw [← Measure.compProd_withDensity hf_meas]
    exact Measure.compProd_congr hκ
  have hrn : (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p ↦ f p.1 p.2 := by
    conv_lhs => rw [← hwd]
    exact Measure.rnDeriv_withDensity _ hf_meas
  -- unfold both sides and use Fubini for the composition-product
  rw [klDiv_eq_lintegral_klFun_of_ac hac']
  have hmeas : Measurable (fun p : α × β ↦ ENNReal.ofReal (klFun ((f p.1 p.2).toReal))) :=
    ENNReal.measurable_ofReal.comp (measurable_klFun.comp
      (ENNReal.measurable_toReal.comp hf_meas))
  calc ∫⁻ p, ENNReal.ofReal (klFun (((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal)) ∂(μ ⊗ₘ η)
      = ∫⁻ p, ENNReal.ofReal (klFun ((f p.1 p.2).toReal)) ∂(μ ⊗ₘ η) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hrn] with p hp
        rw [hp]
    _ = ∫⁻ a, ∫⁻ y, ENNReal.ofReal (klFun ((f a y).toReal)) ∂(η a) ∂μ := by
        rw [Measure.lintegral_compProd hmeas]
    _ = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hac] with a ha
        rw [klDiv_eq_lintegral_klFun_of_ac ha]
        refine lintegral_congr_ae ?_
        filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)] with y hy
        rw [hf]
        rw [hy]
