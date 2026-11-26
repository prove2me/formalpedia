-- Prove2me | solution 1 for ReweightedNPMLE.gamma_max_coordinate_concentration
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:12:55.669807+00:00
-- url     : https://prove2.me/submissions/d4f20b63-38d8-4355-9490-156efaf9a3d4

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic
import Theorems.Thm_ReweightedNPMLE_finite_coordinate_union_bound_real
import Theorems.Thm_ReweightedNPMLE_gamma_coordinate_concentration_of_lt_one
import Theorems.Thm_ReweightedNPMLE_gamma_coordinate_concentration_one

-- Inline helpers preserved from ReweightedNPMLE.GammaDistribution.
section
/-!
# Gamma moment generating function and coordinate tails

The paper uses shape--rate Gamma variables.  This file connects the scalar
logarithm inequalities in `GammaBounds` to mathlib's actual
`ProbabilityTheory.gammaMeasure`.
-/

open MeasureTheory Real Set
open ProbabilityTheory

namespace ReweightedNPMLE







































/-- The manuscript's two-sided Gamma coordinate concentration inequality. -/
theorem gamma_coordinate_concentration {a t : ℝ}
    (ha : 0 < a) (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    (gammaMeasure a a).real {x | |x - 1| > t} ≤
      2 * Real.exp (-a * t ^ 2 / 4) := by
  rcases ht₁.eq_or_lt with rfl | htlt
  · convert gamma_coordinate_concentration_one ha using 1 <;> ring
  · exact gamma_coordinate_concentration_of_lt_one ha ht₀ htlt





end ReweightedNPMLE
end

/-!
# Gamma moment generating function and coordinate tails

The paper uses shape--rate Gamma variables.  This file connects the scalar
logarithm inequalities in `GammaBounds` to mathlib's actual
`ProbabilityTheory.gammaMeasure`.
-/

open MeasureTheory Real Set
open ProbabilityTheory

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Union-bound form of Gamma concentration for an independent product draw.
This is the coordinate-maximum inequality used in both weighting regimes. -/
theorem solution {n : ℕ} {a t : ℝ}
    (ha : 0 < a) (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    (Measure.pi (fun _ : Fin n ↦ gammaMeasure a a)).real
        {w | ∃ i, |w i - 1| > t} ≤
      2 * n * Real.exp (-a * t ^ 2 / 4) := by
  letI : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  let μn : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n ↦ gammaMeasure a a)
  have hcoord (i : Fin n) :
      μn.real {w | |w i - 1| > t} ≤
        2 * Real.exp (-a * t ^ 2 / 4) := by
    have hmeas : MeasurableSet {x : ℝ | |x - 1| > t} := by
      exact measurableSet_lt measurable_const
        ((continuous_abs.comp (continuous_id.sub continuous_const)).measurable)
    have hpre : {w : Fin n → ℝ | |w i - 1| > t} =
        Function.eval i ⁻¹' {x : ℝ | |x - 1| > t} := rfl
    rw [hpre, measureReal_def,
      (measurePreserving_eval (fun _ : Fin n ↦ gammaMeasure a a) i).measure_preimage
        hmeas.nullMeasurableSet]
    exact gamma_coordinate_concentration ha ht₀ ht₁
  have h := finite_coordinate_union_bound_real μn
    (fun i w ↦ w i) (t := t) (b := 2 * Real.exp (-a * t ^ 2 / 4)) hcoord
  change μn.real {w | ∃ i, |w i - 1| > t} ≤ _
  calc
    μn.real {w | ∃ i, |w i - 1| > t} ≤
        n * (2 * Real.exp (-a * t ^ 2 / 4)) := h
    _ = 2 * n * Real.exp (-a * t ^ 2 / 4) := by ring
