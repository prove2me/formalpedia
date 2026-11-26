-- Prove2me | solution 1 for ReweightedNPMLE.gaussianLocationMixtureLaw_radius_tail
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:09:12.673991+00:00
-- url     : https://prove2.me/submissions/d844f5c3-1497-47ed-b447-5a8d48e577a6

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Theorems.Thm_ReweightedNPMLE_euclidean_norm_le_sqrt_card_mul_of_abs_coord_le
import Theorems.Thm_ReweightedNPMLE_gaussianProduct_max_coordinate_tail

-- Inline helpers preserved from ReweightedNPMLE.GaussianRadius.
section
/-!
# Gaussian radius bounds

Chernoff and finite-union estimates for the radius event in the likelihood-net
argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace ReweightedNPMLE







/-- Euclidean norm tail for a standard Gaussian product. -/
theorem gaussianProduct_euclidean_norm_tail (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)).real
        {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} ≤
      2 * d * Real.exp (-t ^ 2 / 2) := by
  have hsubset :
      {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} ⊆
        {z : Fin d → ℝ | ∃ i, |z i| > t} := by
    intro z hz
    by_contra h
    simp only [Set.mem_setOf_eq, not_exists, not_lt] at h
    exact (not_le_of_gt hz)
      (euclidean_norm_le_sqrt_card_mul_of_abs_coord_le z ht.le h)
  exact (measureReal_mono hsubset (by finiteness)).trans
    (gaussianProduct_max_coordinate_tail d ht)



















end ReweightedNPMLE
end

/-!
# Gaussian radius bounds

Chernoff and finite-union estimates for the radius event in the likelihood-net
argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

open ReweightedNPMLE
open ReweightedNPMLE in
/-- A compactly bounded random location shifts the standard Gaussian radius
threshold by at most `S`. -/
theorem solution
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    {S t : ℝ} (hϑS : ∀ a, ‖ϑ a‖ ≤ S) (ht : 0 < t) :
    (gaussianLocationMixtureLaw μ ϑ).real
        {x : Point d | ‖x‖ > S + Real.sqrt d * t} ≤
      2 * d * Real.exp (-t ^ 2 / 2) := by
  let γd : Measure (Fin d → ℝ) :=
    Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)
  let shift : Θ × (Fin d → ℝ) → Point d :=
    fun q ↦ ϑ q.1 + WithLp.toLp 2 q.2
  have hshift : Measurable shift :=
    measurable_gaussianLocationMixtureSample ϑ hϑmeas
  have hbad : MeasurableSet {x : Point d | ‖x‖ > S + Real.sqrt d * t} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have htail : MeasurableSet
      {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hsubset : shift ⁻¹' {x : Point d | ‖x‖ > S + Real.sqrt d * t} ⊆
      Set.univ ×ˢ
        {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} := by
    intro q hq
    have hsum : ‖shift q‖ ≤ ‖ϑ q.1‖ + ‖WithLp.toLp 2 q.2‖ :=
      norm_add_le _ _
    have hnoise : Real.sqrt d * t < ‖WithLp.toLp 2 q.2‖ := by
      by_contra h
      have hle : ‖WithLp.toLp 2 q.2‖ ≤ Real.sqrt d * t := le_of_not_gt h
      have : ‖shift q‖ ≤ S + Real.sqrt d * t :=
        hsum.trans (add_le_add (hϑS q.1) hle)
      exact (not_le_of_gt hq) this
    exact ⟨Set.mem_univ _, hnoise⟩
  change ((μ.prod γd).map shift).real
      {x : Point d | ‖x‖ > S + Real.sqrt d * t} ≤ _
  rw [map_measureReal_apply hshift hbad]
  calc
    (μ.prod γd).real
        (shift ⁻¹' {x : Point d | ‖x‖ > S + Real.sqrt d * t}) ≤
        (μ.prod γd).real (Set.univ ×ˢ
          {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t}) :=
      measureReal_mono hsubset (by finiteness)
    _ = μ.real Set.univ * γd.real
        {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} :=
      measureReal_prod_prod _ _
    _ = γd.real
        {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} := by simp
    _ ≤ 2 * d * Real.exp (-t ^ 2 / 2) :=
      gaussianProduct_euclidean_norm_tail d ht
