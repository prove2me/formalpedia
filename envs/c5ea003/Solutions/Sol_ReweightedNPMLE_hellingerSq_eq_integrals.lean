-- Prove2me | solution 1 for ReweightedNPMLE.hellingerSq_eq_integrals
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:04:08.047769+00:00
-- url     : https://prove2.me/submissions/7df89fec-0076-4837-a3e7-773bcca5c6f7

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





theorem sqrt_sub_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 = a + b - 2 * Real.sqrt (a * b) := by
  rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_mul ha]
  ring



















































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
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ) :
    hellingerSq μ p q =
      (∫ x, p x ∂μ) + (∫ x, q x ∂μ) - 2 * hellingerAffinity μ p q := by
  rw [hellingerSq, hellingerAffinity]
  calc
    (∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂μ) =
        ∫ x, (p x + q x - 2 * Real.sqrt (p x * q x)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ sqrt_sub_sq (hp x) (hq x)
    _ = (∫ x, p x ∂μ) + (∫ x, q x ∂μ) -
        2 * ∫ x, Real.sqrt (p x * q x) ∂μ := by
      rw [integral_sub (f := fun x ↦ p x + q x)
          (g := fun x ↦ 2 * Real.sqrt (p x * q x))
          (hpint.add hqint) (haint.const_mul 2),
        integral_add hpint hqint, integral_const_mul]
