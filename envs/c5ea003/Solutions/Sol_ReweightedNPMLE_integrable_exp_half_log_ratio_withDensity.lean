-- Prove2me | solution 1 for ReweightedNPMLE.integrable_exp_half_log_ratio_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:05:35.112997+00:00
-- url     : https://prove2.me/submissions/ff97cd1e-219a-4c5e-afb0-bc93e7850ac0

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
import Theorems.Thm_ReweightedNPMLE_density_mul_exp_half_log_ratio

/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Integrability form of the same change-of-density calculation. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hqmeas : Measurable q) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ) :
    Integrable (fun x ↦ Real.exp (Real.log (p x / q x) / 2))
      (μ.withDensity fun x ↦ ENNReal.ofReal (q x)) := by
  rw [integrable_withDensity_iff hqmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  apply haint.congr
  exact Filter.Eventually.of_forall fun x ↦ by
    dsimp only
    rw [ENNReal.toReal_ofReal (hq x).le]
    calc
      Real.sqrt (p x * q x) =
          q x * Real.exp (Real.log (p x / q x) / 2) :=
        (density_mul_exp_half_log_ratio (hp x) (hq x)).symm
      _ = Real.exp (Real.log (p x / q x) / 2) * q x := mul_comm _ _
