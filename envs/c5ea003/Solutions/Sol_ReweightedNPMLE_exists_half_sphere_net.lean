-- Prove2me | solution 1 for ReweightedNPMLE.exists_half_sphere_net
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:09:41.53341+00:00
-- url     : https://prove2.me/submissions/87a36ae8-637d-481f-a0bf-51461d2f8512

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_half_separated_sphere_card_le_five_pow

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

open ReweightedNPMLE

















/-! ### A Euclidean half-net with the paper's `5 ^ r` cardinality bound -/
open ReweightedNPMLE in
/-- Every nontrivial finite-dimensional real inner-product space has an internal half-net of its
unit sphere with at most `5 ^ d` points. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] :
    ∃ N : Finset E,
      N.card ≤ 5 ^ Module.finrank ℝ E ∧
      (∀ v ∈ N, ‖v‖ = 1) ∧
      ∀ u : E, ‖u‖ = 1 → ∃ v ∈ N, dist u v ≤ (1 / 2 : ℝ) := by
  let S : Set E := Metric.sphere (0 : E) 1
  obtain ⟨T, _hTS, hTfinite, hTcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact
      (ε := (1 / 4 : ℝ≥0)) (by norm_num) (isCompact_sphere (0 : E) 1)
  have hpack_le : Metric.packingNumber (1 / 2 : ℝ≥0) S ≤ T.encard := by
    calc
      Metric.packingNumber (1 / 2 : ℝ≥0) S =
          Metric.packingNumber (2 * (1 / 4 : ℝ≥0)) S := by norm_num
      _ ≤ Metric.externalCoveringNumber (1 / 4 : ℝ≥0) S :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ T.encard := hTcover.externalCoveringNumber_le_encard
  have hpack : Metric.packingNumber (1 / 2 : ℝ≥0) S ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hpack_le (Set.encard_lt_top_iff.mpr hTfinite))
  let C : Set E := Metric.maximalSeparatedSet (1 / 2 : ℝ≥0) S
  have hCfinite : C.Finite := by
    rw [← Set.encard_ne_top_iff]
    rw [show C.encard = Metric.packingNumber (1 / 2 : ℝ≥0) S by
      exact Metric.encard_maximalSeparatedSet hpack]
    exact hpack
  let N : Finset E := hCfinite.toFinset
  have hNmem {x : E} : x ∈ N ↔ x ∈ C := hCfinite.mem_toFinset
  have hNunit : ∀ x ∈ N, ‖x‖ = 1 := by
    intro x hx
    have hxS : x ∈ S := Metric.maximalSeparatedSet_subset (hNmem.mp hx)
    simpa [S, Metric.mem_sphere, dist_zero_right] using hxS
  have hNsep : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → (1 / 2 : ℝ) < dist x y := by
    intro x hx y hy hxy
    have h := Metric.isSeparated_maximalSeparatedSet
      (hNmem.mp hx) (hNmem.mp hy) hxy
    change (↑(1 / 2 : ℝ≥0) : ℝ≥0∞) < edist x y at h
    rw [edist_dist, ENNReal.coe_nnreal_eq] at h
    exact (ENNReal.ofReal_lt_ofReal_iff').mp h |>.1
  refine ⟨N, half_separated_sphere_card_le_five_pow N hNunit hNsep,
    hNunit, ?_⟩
  intro u hu
  have huS : u ∈ S := by simpa [S, Metric.mem_sphere, dist_zero_right]
  obtain ⟨v, hvC, huv⟩ := Metric.isCover_maximalSeparatedSet hpack huS
  refine ⟨v, hNmem.mpr hvC, ?_⟩
  change edist u v ≤ (↑(1 / 2 : ℝ≥0) : ℝ≥0∞) at huv
  rw [edist_dist, ENNReal.coe_nnreal_eq] at huv
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp huv
