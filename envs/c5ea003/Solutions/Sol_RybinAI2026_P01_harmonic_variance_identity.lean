-- Prove2me | solution 1 for RybinAI2026.P01.harmonic_variance_identity
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-10T14:52:21.582566+00:00
-- url     : https://prove2.me/submissions/2b97cadc-a331-4b22-9052-a03dac3dabe7

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

open MeasureTheory

namespace P01HarmonicVariance

theorem integrable_continuous_compact
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    [CompactSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end P01HarmonicVariance

theorem solution
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    [CompactSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (k r : α → ℝ) (hk : Continuous k) (hr : Continuous r)
    (hrpos : ∀ x, 0 < r x) :
    (∫ x, k x*r x ∂μ)*(∫ x, k x/r x ∂μ)-(∫ x, k x ∂μ)^2 =
      (1/2 : ℝ) * ∫ z : α × α,
        k z.1*k z.2*(r z.1-r z.2)^2/(r z.1*r z.2) ∂(μ.prod μ) := by
  have hki : Integrable k μ := P01HarmonicVariance.integrable_continuous_compact hk
  have hkri : Integrable (fun x => k x*r x) μ :=
    P01HarmonicVariance.integrable_continuous_compact (hk.mul hr)
  have hkdi : Integrable (fun x => k x/r x) μ :=
    P01HarmonicVariance.integrable_continuous_compact
      (hk.div hr (fun x => (hrpos x).ne'))
  have hterm1 : Integrable
      (fun z : α × α => (k z.1*r z.1)*(k z.2/r z.2)) (μ.prod μ) :=
    hkri.mul_prod hkdi
  have hterm2 : Integrable
      (fun z : α × α => (k z.1/r z.1)*(k z.2*r z.2)) (μ.prod μ) :=
    hkdi.mul_prod hkri
  have hterm3 : Integrable
      (fun z : α × α => 2*(k z.1*k z.2)) (μ.prod μ) :=
    (hki.mul_prod hki).const_mul 2
  have hexpand :
      (∫ z : α × α,
        k z.1*k z.2*(r z.1-r z.2)^2/(r z.1*r z.2) ∂(μ.prod μ)) =
      ∫ z : α × α,
        (k z.1*r z.1)*(k z.2/r z.2) +
          (k z.1/r z.1)*(k z.2*r z.2) -
          2*(k z.1*k z.2) ∂(μ.prod μ) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      field_simp [(hrpos z.1).ne', (hrpos z.2).ne']
      ring
  have hadd := integral_add hterm1 hterm2
  have hsub := integral_sub (hterm1.add hterm2) hterm3
  simp only [Pi.add_apply] at hadd hsub
  have hprod1 := integral_prod_mul (μ := μ) (ν := μ)
    (fun x => k x*r x) (fun x => k x/r x)
  have hprod2 := integral_prod_mul (μ := μ) (ν := μ)
    (fun x => k x/r x) (fun x => k x*r x)
  have hprod3 := integral_prod_mul (μ := μ) (ν := μ) k k
  rw [hexpand, hsub, hadd, integral_const_mul, hprod1, hprod2, hprod3]
  ring
