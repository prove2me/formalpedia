-- Prove2me | solution 1 for ReweightedNPMLE.half_separated_sphere_card_le_five_pow
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:08:45.889817+00:00
-- url     : https://prove2.me/submissions/37bf6eaa-b373-4c0a-80f5-4bf2ab26d503

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

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

open ReweightedNPMLE

















/-! ### A Euclidean half-net with the paper's `5 ^ r` cardinality bound -/
open ReweightedNPMLE in
/-- A half-separated subset of a finite-dimensional unit sphere has at most `5 ^ d` points.
This is the standard disjoint-ball volume argument behind the paper's net bound. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (C : Finset E)
    (hSphere : ∀ x ∈ C, ‖x‖ = 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → (1 / 2 : ℝ) < dist x y) :
    C.card ≤ 5 ^ Module.finrank ℝ E := by
  have hdisj : (C : Set E).PairwiseDisjoint
      (fun x ↦ Metric.ball x (1 / 4 : ℝ)) := by
    intro x hx y hy hxy
    exact Metric.ball_disjoint_ball (by nlinarith [hsep x hx y hy hxy])
  have hunion : (⋃ x ∈ C, Metric.ball x (1 / 4 : ℝ)) ⊆
      Metric.ball (0 : E) (5 / 4 : ℝ) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx⟩ := hz
    obtain ⟨hxC, hzx⟩ := hx
    rw [Metric.mem_ball] at hzx ⊢
    rw [dist_zero_right]
    calc
      ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ < (1 / 4 : ℝ) + 1 := by
        rw [hSphere x hxC]
        simpa [dist_eq_norm] using hzx
      _ = 5 / 4 := by norm_num
  have hmeasure :
      ∑ x ∈ C, volume (Metric.ball x (1 / 4 : ℝ)) ≤
        volume (Metric.ball (0 : E) (5 / 4 : ℝ)) := by
    rw [← measure_biUnion_finset hdisj (fun _ _ ↦ measurableSet_ball)]
    exact measure_mono hunion
  simp_rw [Measure.addHaar_ball_of_pos volume _
    (by norm_num : (0 : ℝ) < 1 / 4)] at hmeasure
  rw [Measure.addHaar_ball_of_pos volume 0
    (by norm_num : (0 : ℝ) < 5 / 4)] at hmeasure
  simp only [Finset.sum_const, nsmul_eq_mul] at hmeasure
  let d := Module.finrank ℝ E
  have hb0 : volume (Metric.ball (0 : E) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : E) (by norm_num)).ne'
  have hbtop : volume (Metric.ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hcancel : (C.card : ENNReal) * ENNReal.ofReal ((1 / 4 : ℝ) ^ d) ≤
      ENNReal.ofReal ((5 / 4 : ℝ) ^ d) := by
    apply (ENNReal.mul_le_mul_iff_left hb0 hbtop).mp
    simpa only [d, mul_assoc] using hmeasure
  have hreal : (C.card : ℝ) ≤ (5 : ℝ) ^ d := by
    have h := ENNReal.toReal_le_of_le_ofReal
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4) d) hcancel
    simpa [div_eq_mul_inv, mul_pow] using h
  exact_mod_cast hreal
