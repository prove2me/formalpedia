-- Prove2me | solution 1 for ReweightedNPMLE.measurableSet_gaussianStructuralFailure
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:17:22.027914+00:00
-- url     : https://prove2.me/submissions/b53635bf-37de-4ce2-afa4-0e462e577daa

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_CompactOptimizerEvents
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianJointEvents
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SmallSupportProbability
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_continuous_gaussianSquaredLogRatioGap
import Theorems.Thm_ReweightedNPMLE_continuous_gaussian_probabilityLogLikelihood_joint
import Theorems.Thm_ReweightedNPMLE_measurableSet_compactOptimizer_nonunique
import Theorems.Thm_ReweightedNPMLE_measurableSet_exists_closed_relation_strict_gap
import Theorems.Thm_ReweightedNPMLE_measurableSet_gaussian_optimizer_support_failure

-- Inline helpers preserved from ReweightedNPMLE.CompactOptimizerEvents.
section
/-!
# Measurable parameterized optimizer events

Continuous optimization on a compact law space has a closed optimizer graph.
Compact projection and countable distance thresholds make failure of
uniqueness and strict optimizer inequalities Borel events. These results are
used to integrate conditional conclusions without assuming a measurable
choice of the conditional good sets.
-/

open Set
open scoped Topology

namespace ReweightedNPMLE



theorem isClosed_compactOptimizerGraph {X M : Type*}
    [TopologicalSpace X] [TopologicalSpace M] (U : X × M → ℝ) (hU : Continuous U) :
    IsClosed (compactOptimizerGraph U) := by
  have heq : compactOptimizerGraph U = ⋂ μ : M, {p | U (p.1, μ) ≤ U p} := by
    ext p
    constructor
    · intro hp
      exact mem_iInter.mpr (fun μ ↦ hp.2 μ (mem_univ μ))
    · intro hp
      exact ⟨mem_univ p.2, fun μ _ ↦ mem_iInter.mp hp μ⟩
  rw [heq]
  exact isClosed_iInter (fun μ ↦ isClosed_le
    (hU.comp (continuous_fst.prodMk continuous_const)) hU)











end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianJointEvents.
section
/-!
# Joint Borel events for Gaussian optimizer laws

All events concern the full probability-law optimizer space. Compact law
projection proves measurability of nonuniqueness, support failure, and
ordinary likelihood and fitted-log failures jointly in data and weights.
-/

open Set MeasureTheory
open scoped Topology BigOperators

namespace ReweightedNPMLE







theorem continuous_gaussianProbabilityLogLikelihood {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    Continuous (gaussianProbabilityLogLikelihood (n := n) θ) :=
  continuous_gaussian_probabilityLogLikelihood_joint θ hθ

theorem measurableSet_gaussian_optimizer_nonunique {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    MeasurableSet {p : GaussianDataWeight d n | ∃ μ ν : ProbabilityMeasure Θ,
      μ ∈ gaussianProbabilityOptimizerSet θ p ∧ ν ∈ gaussianProbabilityOptimizerSet θ p ∧ μ ≠ ν} := by
  letI : MetricSpace (ProbabilityMeasure Θ) := TopologicalSpace.metrizableSpaceMetric _
  exact measurableSet_compactOptimizer_nonunique _ (continuous_gaussianProbabilityLogLikelihood θ hθ)





theorem isClosed_gaussianOptimizerComparisonGraph {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    IsClosed (gaussianOptimizerComparisonGraph (n := n) θ) := by
  have hgraph := isClosed_compactOptimizerGraph _ (continuous_gaussianProbabilityLogLikelihood (n := n) θ hθ)
  have hmap₁ : Continuous (fun p : GaussianDataWeight d n ×
      (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦ (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hmap₀ : Continuous (fun p : GaussianDataWeight d n ×
      (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦ ((p.1.1, (1 : Fin n → ℝ)), p.2.2)) :=
    ((continuous_fst.comp continuous_fst).prodMk continuous_const).prodMk
      (continuous_snd.comp continuous_snd)
  exact (hgraph.preimage hmap₁).inter (hgraph.preimage hmap₀)



theorem continuous_gaussianOrdinaryLikelihoodGap {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    Continuous (gaussianOrdinaryLikelihoodGap (n := n) θ) := by
  have hU := continuous_gaussianProbabilityLogLikelihood (n := n) θ hθ
  have hmap₀ : Continuous (fun p : GaussianDataWeight d n ×
      (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦ ((p.1.1, (1 : Fin n → ℝ)), p.2.2)) :=
    ((continuous_fst.comp continuous_fst).prodMk continuous_const).prodMk
      (continuous_snd.comp continuous_snd)
  have hmap₁ : Continuous (fun p : GaussianDataWeight d n ×
      (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦ ((p.1.1, (1 : Fin n → ℝ)), p.2.1)) :=
    ((continuous_fst.comp continuous_fst).prodMk continuous_const).prodMk
      (continuous_fst.comp continuous_snd)
  exact (hU.comp hmap₀).sub (hU.comp hmap₁)

theorem measurableSet_gaussian_optimizer_likelihood_failure {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) (t : ℝ) :
    MeasurableSet {p : GaussianDataWeight d n | ∃ μ : ProbabilityMeasure Θ × ProbabilityMeasure Θ,
      (p, μ) ∈ gaussianOptimizerComparisonGraph θ ∧ t < gaussianOrdinaryLikelihoodGap θ (p, μ)} := by
  exact measurableSet_exists_closed_relation_strict_gap _
    (isClosed_gaussianOptimizerComparisonGraph θ hθ) (fun p ↦ gaussianOrdinaryLikelihoodGap θ p - t)
    ((continuous_gaussianOrdinaryLikelihoodGap θ hθ).sub continuous_const) |>.congr
      (by ext p; simp only [mem_setOf_eq, sub_pos])





theorem measurableSet_gaussian_optimizer_log_fit_failure {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) (t : ℝ) :
    MeasurableSet {p : GaussianDataWeight d n | ∃ μ : ProbabilityMeasure Θ × ProbabilityMeasure Θ,
      (p, μ) ∈ gaussianOptimizerComparisonGraph θ ∧ t < gaussianSquaredLogRatioGap θ (p, μ)} := by
  exact measurableSet_exists_closed_relation_strict_gap _
    (isClosed_gaussianOptimizerComparisonGraph θ hθ) (fun p ↦ gaussianSquaredLogRatioGap θ p - t)
    ((continuous_gaussianSquaredLogRatioGap θ hθ).sub continuous_const) |>.congr
      (by ext p; simp only [mem_setOf_eq, sub_pos])







end ReweightedNPMLE
end

/-!
# Joint Borel events for Gaussian optimizer laws

All events concern the full probability-law optimizer space. Compact law
projection proves measurability of nonuniqueness, support failure, and
ordinary likelihood and fitted-log failures jointly in data and weights.
-/

open Set MeasureTheory
open scoped Topology BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) {R : ℝ} (hR : 0 ≤ R) (t a : ℝ) :
    MeasurableSet (gaussianStructuralFailure (n := n) θ R t a) := by
  have hcoord : MeasurableSet {p : GaussianDataWeight d n | ∀ i, |p.2 i - 1| ≤ a} := by
    have heq : {p : GaussianDataWeight d n | ∀ i, |p.2 i - 1| ≤ a} =
        ⋂ i : Fin n, {p : GaussianDataWeight d n | |p.2 i - 1| ≤ a} := by ext p; simp
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    have hi : Continuous (fun p : GaussianDataWeight d n ↦ |p.2 i - 1|) :=
      continuous_abs.comp (((continuous_apply i).comp continuous_snd).sub continuous_const)
    exact measurableSet_le hi.measurable measurable_const
  have hpos : MeasurableSet {p : GaussianDataWeight d n | p.2 ∈ positiveVectors n} := by
    have heq : {p : GaussianDataWeight d n | p.2 ∈ positiveVectors n} =
        ⋂ i : Fin n, {p : GaussianDataWeight d n | 0 < p.2 i} := by ext p; simp [positiveVectors]
    rw [heq]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_lt measurable_const
      ((measurable_pi_apply i).comp measurable_snd))
  have hbadcoord : MeasurableSet {p : GaussianDataWeight d n |
      ¬((∀ i, |p.2 i - 1| ≤ a) ∧ p.2 ∈ positiveVectors n)} := (hcoord.inter hpos).compl
  exact (((hbadcoord.union (measurableSet_gaussian_optimizer_nonunique θ hθ)).union
    (measurableSet_gaussian_optimizer_support_failure θ hθ hR)).union
      (measurableSet_gaussian_optimizer_likelihood_failure θ hθ t)).union
        (measurableSet_gaussian_optimizer_log_fit_failure θ hθ t)
