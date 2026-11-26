-- Prove2me | solution 1 for ReweightedNPMLE.notMem_gaussianStructuralFailure_of_unique_optimizer
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:15:27.49738+00:00
-- url     : https://prove2.me/submissions/f303b3dd-6849-496b-9e9e-8f4c4a582ea0

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
    [TopologicalSpace Θ] [MeasurableSpace Θ] {d n : ℕ}
    (θ : Θ → Point d) (x : Fin n → Point d) (w : Fin n → ℝ) (R t a : ℝ)
    (hcoord : ∀ i, |w i - 1| ≤ a) (hw : w ∈ positiveVectors n)
    (μ : ProbabilityMeasure Θ) (hunique : gaussianProbabilityOptimizerSet θ (x, w) = {μ})
    (hfinite : (μ : Measure Θ).support.Finite) (hcard : ((μ : Measure Θ).support.ncard : ℝ) ≤ R)
    (hcompare : ∀ μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1),
      gaussianOrdinaryLikelihoodGap θ ((x, w), (μ, μ₀)) ≤ t ∧
      gaussianSquaredLogRatioGap θ ((x, w), (μ, μ₀)) ≤ t) :
    (x, w) ∉ gaussianStructuralFailure θ R t a := by
  intro hbad
  simp only [gaussianStructuralFailure, mem_union, mem_setOf_eq] at hbad
  rcases hbad with (((hweight | hnonunique) | hsupport) | hgap) | hlog
  · exact hweight ⟨hcoord, hw⟩
  · obtain ⟨μ₁, μ₂, hμ₁, hμ₂, hneq⟩ := hnonunique
    rw [hunique, mem_singleton_iff] at hμ₁ hμ₂
    exact hneq (hμ₁.trans hμ₂.symm)
  · obtain ⟨ν, hν, hfail⟩ := hsupport
    rw [hunique, mem_singleton_iff] at hν
    subst ν
    exact hfail ⟨hfinite, hcard⟩
  · obtain ⟨⟨ν, μ₀⟩, hν, hfail⟩ := hgap
    have hgraph : ν ∈ gaussianProbabilityOptimizerSet θ (x, w) ∧
        μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1) := hν
    rw [hunique, mem_singleton_iff] at hgraph
    obtain ⟨rfl, hμ₀⟩ := hgraph
    exact (not_lt_of_ge (hcompare μ₀ hμ₀).1) hfail
  · obtain ⟨⟨ν, μ₀⟩, hν, hfail⟩ := hlog
    have hgraph : ν ∈ gaussianProbabilityOptimizerSet θ (x, w) ∧
        μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1) := hν
    rw [hunique, mem_singleton_iff] at hgraph
    obtain ⟨rfl, hμ₀⟩ := hgraph
    exact (not_lt_of_ge (hcompare μ₀ hμ₀).2) hfail
