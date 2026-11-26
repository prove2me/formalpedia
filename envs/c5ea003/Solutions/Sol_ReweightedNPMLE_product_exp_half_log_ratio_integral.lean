-- Prove2me | solution 1 for ReweightedNPMLE.product_exp_half_log_ratio_integral
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:05:21.703218+00:00
-- url     : https://prove2.me/submissions/57910142-ec2a-42f2-a6c5-b9e798c8f8dc

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













































/-- Exponentiating half of a finite log-likelihood ratio turns its sum into
the product of the coordinatewise square-root likelihood ratios. -/
theorem exp_half_sum_log_ratio_eq_prod {Ω : Type*} {n : ℕ}
    (p q : Ω → ℝ) (x : Fin n → Ω) :
    Real.exp ((∑ i, Real.log (p (x i) / q (x i))) / 2) =
      ∏ i, Real.exp (Real.log (p (x i) / q (x i)) / 2) := by
  rw [div_eq_mul_inv, Finset.sum_mul, Real.exp_sum]
  simp only [div_eq_mul_inv]











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
/-- Independence factors the square-root likelihood-ratio expectation into a
power of its one-observation expectation. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (ν : Measure Ω) [SigmaFinite ν] (p q : Ω → ℝ) :
    ∫ x : Fin n → Ω,
        Real.exp ((∑ i, Real.log (p (x i) / q (x i))) / 2)
        ∂Measure.pi (fun _ : Fin n ↦ ν) =
      (∫ y, Real.exp (Real.log (p y / q y) / 2) ∂ν) ^ n := by
  calc
    _ = ∫ x : Fin n → Ω,
        ∏ i, Real.exp (Real.log (p (x i) / q (x i)) / 2)
        ∂Measure.pi (fun _ : Fin n ↦ ν) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦
            exp_half_sum_log_ratio_eq_prod p q x
    _ = _ := by
      simpa using
        (integral_fintype_prod_eq_pow (ι := Fin n)
          (μ := ν) (fun y ↦ Real.exp (Real.log (p y / q y) / 2)))
