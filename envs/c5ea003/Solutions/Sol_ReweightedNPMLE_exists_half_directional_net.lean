-- Prove2me | solution 1 for ReweightedNPMLE.exists_half_directional_net
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:10:23.075709+00:00
-- url     : https://prove2.me/submissions/a7043a6a-6da1-463d-a7b8-1ebecfab37cf

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
import Theorems.Thm_ReweightedNPMLE_exists_half_sphere_net

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

open ReweightedNPMLE

















/-! ### A Euclidean half-net with the paper's `5 ^ r` cardinality bound -/
open ReweightedNPMLE in
/-- A half-net controls the norm by twice one of its directional inner products. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] :
    ∃ N : Finset E,
      N.card ≤ 5 ^ Module.finrank ℝ E ∧
      (∀ v ∈ N, ‖v‖ = 1) ∧
      ∀ y : E, ∃ v ∈ N, ‖y‖ ≤ 2 * inner ℝ v y := by
  obtain ⟨N, hNcard, hNunit, hNcover⟩ := exists_half_sphere_net (E := E)
  refine ⟨N, hNcard, hNunit, ?_⟩
  intro y
  by_cases hy : y = 0
  · obtain ⟨z, hz⟩ := exists_ne (0 : E)
    let u : E := (‖z‖⁻¹ : ℝ) • z
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hz
    obtain ⟨v, hvN, _hvdist⟩ := hNcover u hu
    exact ⟨v, hvN, by simp [hy]⟩
  · let u : E := (‖y‖⁻¹ : ℝ) • y
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hy
    obtain ⟨v, hvN, hvdist⟩ := hNcover u hu
    have hv : ‖v‖ = 1 := hNunit v hvN
    have hdistnorm : ‖u - v‖ ≤ (1 / 2 : ℝ) := by
      simpa [dist_eq_norm] using hvdist
    have hnormsq := norm_sub_sq_real u v
    have hsquare : ‖u - v‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      nlinarith [norm_nonneg (u - v)]
    have huv : (1 / 2 : ℝ) ≤ inner ℝ v u := by
      rw [hu, hv] at hnormsq
      rw [real_inner_comm]
      nlinarith
    have hyrep : y = ‖y‖ • u := by
      dsimp [u]
      rw [smul_smul]
      simp [hy]
    refine ⟨v, hvN, ?_⟩
    have hynorm : 0 ≤ ‖y‖ := norm_nonneg y
    have hinner : inner ℝ v y = ‖y‖ * inner ℝ v u := by
      calc
        inner ℝ v y = inner ℝ v (‖y‖ • u) := congrArg (inner ℝ v) hyrep
        _ = ‖y‖ * inner ℝ v u := by rw [inner_smul_right]
    rw [hinner]
    nlinarith
