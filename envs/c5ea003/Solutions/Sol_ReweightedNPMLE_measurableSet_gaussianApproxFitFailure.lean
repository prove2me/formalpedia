-- Prove2me | solution 1 for ReweightedNPMLE.measurableSet_gaussianApproxFitFailure
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:15:24.411082+00:00
-- url     : https://prove2.me/submissions/5c97a4dd-e9c8-4c7d-9f3d-980af227d337

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_CompactOptimizerEvents
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedGeometry
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedLocalization
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_FullEffectiveDimension
import Definitions.Def_ReweightedNPMLE_GammaEffectiveEvent
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianApproxJointEvents
import Definitions.Def_ReweightedNPMLE_GaussianExactRegularization
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianGenericity
import Definitions.Def_ReweightedNPMLE_GaussianIncidence
import Definitions.Def_ReweightedNPMLE_GaussianJointConsistency
import Definitions.Def_ReweightedNPMLE_GaussianJointEvents
import Definitions.Def_ReweightedNPMLE_GaussianJointTheorems
import Definitions.Def_ReweightedNPMLE_GaussianMainTheorem
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianNearMLE
import Definitions.Def_ReweightedNPMLE_GaussianNearMLERate
import Definitions.Def_ReweightedNPMLE_GaussianPaperScales
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_GaussianSampling
import Definitions.Def_ReweightedNPMLE_GaussianStructural
import Definitions.Def_ReweightedNPMLE_GaussianTinyJoint
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_IncidenceJacobian
import Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_SmallSupportProbability
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_continuous_gaussianSquaredLogRatioGap
import Theorems.Thm_ReweightedNPMLE_continuous_gaussian_probabilityLogLikelihood_joint
import Theorems.Thm_ReweightedNPMLE_measurableSet_exists_closed_relation_strict_gap

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















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianApproxJointEvents.
section
/-! # Borel simultaneous approximate-fit failures

The comparison relation includes a weighted optimizer, an ordinary optimizer,
and an arbitrary attainable approximate mixing law. Closedness and compact
law projection prove joint measurability of the universal fit conclusions.
-/

open Set MeasureTheory
open scoped Topology

namespace ReweightedNPMLE



theorem isClosed_gaussianApproxComparisonGraph {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) (τ : ℝ) :
    IsClosed (gaussianApproxComparisonGraph (n := n) θ τ) := by
  have hmap : Continuous (fun p : GaussianDataWeight d n ×
      ((ProbabilityMeasure Θ × ProbabilityMeasure Θ) × ProbabilityMeasure Θ) ↦ (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hmapw : Continuous (fun p : GaussianDataWeight d n ×
      ((ProbabilityMeasure Θ × ProbabilityMeasure Θ) × ProbabilityMeasure Θ) ↦ (p.1, p.2.1.1)) :=
    continuous_fst.prodMk (continuous_fst.comp (continuous_fst.comp continuous_snd))
  have hmapv : Continuous (fun p : GaussianDataWeight d n ×
      ((ProbabilityMeasure Θ × ProbabilityMeasure Θ) × ProbabilityMeasure Θ) ↦ (p.1, p.2.2)) :=
    continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  have hU := continuous_gaussianProbabilityLogLikelihood (n := n) θ hθ
  exact ((isClosed_gaussianOptimizerComparisonGraph θ hθ).preimage hmap).inter
    (isClosed_le ((hU.comp hmapw).sub continuous_const) (hU.comp hmapv))







end ReweightedNPMLE
end

/-! # Borel simultaneous approximate-fit failures

The comparison relation includes a weighted optimizer, an ordinary optimizer,
and an arbitrary attainable approximate mixing law. Closedness and compact
law projection prove joint measurability of the universal fit conclusions.
-/

open Set MeasureTheory
open scoped Topology

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) (τ t : ℝ) :
    MeasurableSet (gaussianApproxFitFailure (n := n) θ τ t) := by
  letI : MetricSpace (ProbabilityMeasure Θ) := TopologicalSpace.metrizableSpaceMetric _
  have hmap : Continuous (fun p : GaussianDataWeight d n ×
      ((ProbabilityMeasure Θ × ProbabilityMeasure Θ) × ProbabilityMeasure Θ) ↦
      (p.1, (p.2.2, p.2.1.2))) :=
    continuous_fst.prodMk ((continuous_snd.comp continuous_snd).prodMk
      (continuous_snd.comp (continuous_fst.comp continuous_snd)))
  have hgraph := isClosed_gaussianApproxComparisonGraph (n := n) θ hθ τ
  have hgap := measurableSet_exists_closed_relation_strict_gap _ hgraph
    (fun p ↦ gaussianOrdinaryLikelihoodGap θ (p.1, (p.2.2, p.2.1.2)) - t)
    (((continuous_gaussianOrdinaryLikelihoodGap θ hθ).comp hmap).sub continuous_const)
  have hlog := measurableSet_exists_closed_relation_strict_gap _ hgraph
    (fun p ↦ gaussianSquaredLogRatioGap θ (p.1, (p.2.2, p.2.1.2)) - t)
    (((continuous_gaussianSquaredLogRatioGap θ hθ).comp hmap).sub continuous_const)
  exact (hgap.congr (by ext p; simp only [mem_setOf_eq, sub_pos])).union
    (hlog.congr (by ext p; simp only [mem_setOf_eq, sub_pos]))
