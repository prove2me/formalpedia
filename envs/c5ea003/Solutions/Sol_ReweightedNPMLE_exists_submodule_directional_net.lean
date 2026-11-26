-- Prove2me | solution 1 for ReweightedNPMLE.exists_submodule_directional_net
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:11:12.896955+00:00
-- url     : https://prove2.me/submissions/9c81f243-195d-4319-a7c0-e8c958fef7b8

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
import Theorems.Thm_ReweightedNPMLE_exists_half_directional_net

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

open ReweightedNPMLE

















/-! ### A Euclidean half-net with the paper's `5 ^ r` cardinality bound -/
open ReweightedNPMLE in
/-- A rank-`r` Euclidean subspace has the finite directional net required by the projected Gamma
concentration argument. The zero-dimensional case is handled by the singleton `{0}`. -/
theorem solution {n r : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hrank : Module.finrank ℝ V ≤ r) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin n)),
      N.card ≤ 5 ^ r ∧
      (∀ v ∈ N, ∑ i, (v i) ^ 2 ≤ 1) ∧
      ∀ y ∈ V, ∃ v ∈ N, v ∈ V ∧ ‖y‖ ≤ 2 * inner ℝ v y := by
  classical
  by_cases hV : Nontrivial V
  · letI : Nontrivial V := hV
    obtain ⟨Nsub, hNsubcard, hNsubunit, hNsubnet⟩ :=
      exists_half_directional_net (E := V)
    let N : Finset (EuclideanSpace ℝ (Fin n)) :=
      Nsub.image (fun v : V ↦ (v : EuclideanSpace ℝ (Fin n)))
    refine ⟨N, ?_, ?_, ?_⟩
    · calc
        N.card ≤ Nsub.card := Finset.card_image_le
        _ ≤ 5 ^ Module.finrank ℝ V := hNsubcard
        _ ≤ 5 ^ r := pow_le_pow_right' (by norm_num) hrank
    · intro v hv
      simp only [N, Finset.mem_image] at hv
      obtain ⟨z, hzN, rfl⟩ := hv
      rw [← EuclideanSpace.real_norm_sq_eq]
      have hzunit : ‖(z : EuclideanSpace ℝ (Fin n))‖ = 1 := hNsubunit z hzN
      rw [hzunit]
      norm_num
    · intro y hyV
      let ys : V := ⟨y, hyV⟩
      obtain ⟨v, hvNsub, hvbound⟩ := hNsubnet ys
      refine ⟨(v : EuclideanSpace ℝ (Fin n)), ?_, v.2, ?_⟩
      · exact Finset.mem_image.mpr ⟨v, hvNsub, rfl⟩
      · simpa [ys] using hvbound
  · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    refine ⟨{0}, ?_, ?_, ?_⟩
    · simp only [Finset.card_singleton]
      have : 0 < 5 ^ r := pow_pos (by norm_num) r
      omega
    · intro v hv
      simp only [Finset.mem_singleton] at hv
      subst v
      simp
    · intro y hyV
      refine ⟨0, Finset.mem_singleton_self 0, V.zero_mem, ?_⟩
      have hy0 : y = 0 := by
        exact congrArg Subtype.val (Subsingleton.elim (⟨y, hyV⟩ : V) 0)
      simp [hy0]
