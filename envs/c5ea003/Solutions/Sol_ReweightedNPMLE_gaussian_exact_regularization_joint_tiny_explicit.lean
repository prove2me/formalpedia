-- Prove2me | solution 1 for ReweightedNPMLE.gaussian_exact_regularization_joint_tiny_explicit
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:20:10.0779+00:00
-- url     : https://prove2.me/submissions/2f62ae4a-2a32-4ce0-8705-0537b29d2dab

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
import Definitions.Def_ReweightedNPMLE_GaussianExactRegularization
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianGenericity
import Definitions.Def_ReweightedNPMLE_GaussianIncidence
import Definitions.Def_ReweightedNPMLE_GaussianJointEvents
import Definitions.Def_ReweightedNPMLE_GaussianJointTheorems
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
import Theorems.Thm_ReweightedNPMLE_absolutelyContinuous_finiteProduct
import Theorems.Thm_ReweightedNPMLE_compactGaussianMixture_measurable_uniform_nearMLE_event
import Theorems.Thm_ReweightedNPMLE_compactGaussianSampleMeasure_paper_radius_tail
import Theorems.Thm_ReweightedNPMLE_continuous_gaussian_probabilityLogLikelihood_joint
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperLogScale_nonneg_le_log
import Theorems.Thm_ReweightedNPMLE_gaussian_exact_regularization_conditional_tiny
import Theorems.Thm_ReweightedNPMLE_gaussian_probability_optimizer_iff_score_fiber
import Theorems.Thm_ReweightedNPMLE_measurableSet_compactOptimizer_nonunique
import Theorems.Thm_ReweightedNPMLE_measurableSet_exists_closed_relation_strict_gap
import Theorems.Thm_ReweightedNPMLE_measurableSet_gaussian_optimizer_support_failure
import Theorems.Thm_ReweightedNPMLE_measureReal_prod_le_of_uniform_section_bound
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureFiber_nonempty_of_mem_convexHull

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

-- Inline helpers preserved from ReweightedNPMLE.FittedRegularity.
section
/-!
# Regularity of the fitted-value problem

This file proves the analytic regularity part of the paper's effective-dimension
argument.  Variational inequalities yield a quantitative local Lipschitz bound
for the unique fitted vector and its coordinatewise logarithm.  Mathlib's
Rademacher theorem then gives almost-everywhere differentiability.
-/

open Set MeasureTheory Filter
open scoped BigOperators NNReal

namespace ReweightedNPMLE



theorem fittedValueSelection_isMax {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (w : Fin n → ℝ) :
    IsMaxOn C (weightedLogLikelihood w)
      (fittedValueSelection C hCcompact hCnonempty hCpos w) :=
  Classical.choose_spec (exists_fittedValue_maximizer hCcompact hCnonempty hCpos w)







































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianPaperScales.
section
/-!
# Eventual scales for Gaussian exact regularization

The paper's logarithmic effective dimension, balanced Gamma shape, Taylor
rank, and remainder conditions are consequences, rather than assumptions.
Only eventual statements are used: the definitions at small sample sizes
are irrelevant.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace ReweightedNPMLE











theorem eventually_gaussianPaperAugmentedDimension_pos (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0 < gaussianPaperAugmentedDimension d n := by
  filter_upwards [eventually_gaussianPaperLogScale_nonneg_le_log,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with n hs hl
  exact add_pos_of_nonneg_of_pos (pow_nonneg hs.1 d) hl













































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianExactRegularization.
section
/-!
# Gaussian exact regularization

This module assembles the structural Gaussian result at the paper's actual
balanced concentration. Its optimizer sets consist of all probability laws,
not just finite atomic measures. Statistical risk is assembled separately.
-/

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE



theorem gaussianCanonicalFit_isMax {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    {d n : ℕ} (x : Fin n → Point d) (θ : Θ → Point d) (hθ : Continuous θ)
    (w : Fin n → ℝ) :
    IsMaxOn (convexHull ℝ (range (fun a ↦ gaussianScoreFeature x (θ a))))
      (weightedLogLikelihood w) (gaussianCanonicalFit x θ hθ w) :=
  fittedValueSelection_isMax _ _ _ _ w













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

-- Inline helpers preserved from ReweightedNPMLE.GaussianSampling.
section
/-!
# Gaussian sample laws and simultaneous genericity

The iid sample law has a density, is a probability law, and satisfies the
uniform paper-radius tail. The constants do not depend on the true compact
mixing law.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace ReweightedNPMLE







theorem compactGaussianSampleMeasure_absolutelyContinuous {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) (n : ℕ) : compactGaussianSampleMeasure Gstar n ≪ volume := by
  let ν : Measure (Point d) := volume.withDensity
    (fun y ↦ ENNReal.ofReal (compactGaussianMixtureDensity Gstar y))
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    rw [← compactGaussianMixtureLaw_eq_density Gstar]
    exact gaussianLocationMixtureLaw_isProbability _ _ measurable_subtype_coe
  exact absolutelyContinuous_finiteProduct ν volume (withDensity_absolutelyContinuous _ _) n



end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianJointTheorems.
section
/-!
# Exact regularization on one joint probability event

The experiment is the independent product of the actual iid Gaussian-mixture
sample law and the Gamma weight law. A measurable hull of the uniform near-MLE
risk exception suffices: no measurable choice of an optimizing mixing law is
assumed.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE



theorem gaussianProbabilityLogLikelihood_one {d n : ℕ} {K : Set (Point d)}
    (x : Fin n → Point d) (G : ProbabilityMeasure K) :
    gaussianProbabilityLogLikelihood (fun a : K ↦ (a : Point d)) ((x, 1), G) =
      ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) := by
  simp [gaussianProbabilityLogLikelihood, weightedLogLikelihood, probabilityMixtureValue,
    compactGaussianMixtureDensity, gaussianMixture]





end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianTinyJoint.
section
/-! # Joint arbitrarily-small perturbations

The failure event quantifies over all probability laws, so the joint theorem
requires neither a chosen optimizer nor a data-dependent measurable selection.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE



theorem measurableSet_gaussianTinyStructuralFailure {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) {R : ℝ} (hR : 0 ≤ R) (a : ℝ) :
    MeasurableSet (gaussianTinyStructuralFailure (n := n) θ R a) := by
  letI : MetricSpace (ProbabilityMeasure Θ) := TopologicalSpace.metrizableSpaceMetric _
  have hcoord : MeasurableSet {p : GaussianDataWeight d n | ∀ i, |p.2 i - 1| ≤ a} := by
    have heq : {p : GaussianDataWeight d n | ∀ i, |p.2 i - 1| ≤ a} =
        ⋂ i : Fin n, {p : GaussianDataWeight d n | |p.2 i - 1| ≤ a} := by ext p; simp
    rw [heq]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_le
      (continuous_abs.comp (((continuous_apply i).comp continuous_snd).sub continuous_const)).measurable
      measurable_const)
  have hpos : MeasurableSet {p : GaussianDataWeight d n | p.2 ∈ positiveVectors n} := by
    have heq : {p : GaussianDataWeight d n | p.2 ∈ positiveVectors n} =
        ⋂ i : Fin n, {p : GaussianDataWeight d n | 0 < p.2 i} := by ext p; simp [positiveVectors]
    rw [heq]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_lt measurable_const
      ((measurable_pi_apply i).comp measurable_snd))
  have hgap : MeasurableSet {p : GaussianDataWeight d n |
      ∃ μ : ProbabilityMeasure Θ × ProbabilityMeasure Θ,
        μ.1 ∈ gaussianProbabilityOptimizerSet θ p ∧ 1 < gaussianOrdinaryLikelihoodGap θ (p, μ)} := by
    let T : Set (GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) :=
      {p | p.2.1 ∈ gaussianProbabilityOptimizerSet θ p.1}
    have hT : IsClosed T := (isClosed_compactOptimizerGraph _
      (continuous_gaussianProbabilityLogLikelihood θ hθ)).preimage
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have h := measurableSet_exists_closed_relation_strict_gap T hT
      (fun p ↦ gaussianOrdinaryLikelihoodGap θ p - 1)
      ((continuous_gaussianOrdinaryLikelihoodGap θ hθ).sub continuous_const)
    simpa only [T, mem_setOf_eq, sub_pos] using h
  exact (((hcoord.inter hpos).compl.union (measurableSet_gaussian_optimizer_nonunique θ hθ)).union
    (measurableSet_gaussian_optimizer_support_failure θ hθ hR)).union hgap

theorem notMem_gaussianTinyStructuralFailure_of_unique_nearMLE {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] {d n : ℕ}
    (θ : Θ → Point d) (x : Fin n → Point d) (w : Fin n → ℝ) (R a : ℝ)
    (hcoord : ∀ i, |w i - 1| ≤ a) (hpos : w ∈ positiveVectors n)
    (μ : ProbabilityMeasure Θ) (huniq : gaussianProbabilityOptimizerSet θ (x, w) = {μ})
    (hfinite : (μ : Measure Θ).support.Finite) (hcard : ((μ : Measure Θ).support.ncard : ℝ) ≤ R)
    (hnear : ∀ ν : ProbabilityMeasure Θ,
      gaussianProbabilityLogLikelihood θ ((x, 1), ν) - 1 ≤
        gaussianProbabilityLogLikelihood θ ((x, 1), μ)) :
    (x, w) ∉ gaussianTinyStructuralFailure θ R a := by
  intro hbad
  simp only [gaussianTinyStructuralFailure, mem_union, mem_setOf_eq] at hbad
  rcases hbad with ((hweight | hnonunique) | hsupport) | hgap
  · exact hweight ⟨hcoord, hpos⟩
  · obtain ⟨μ₁, μ₂, h₁, h₂, hne⟩ := hnonunique
    rw [huniq, mem_singleton_iff] at h₁ h₂
    exact hne (h₁.trans h₂.symm)
  · obtain ⟨ν, hν, hfail⟩ := hsupport
    rw [huniq, mem_singleton_iff] at hν
    subst ν
    exact hfail ⟨hfinite, hcard⟩
  · obtain ⟨⟨ν, ρ⟩, hν, hfail⟩ := hgap
    rw [huniq, mem_singleton_iff] at hν
    change ν = μ at hν
    subst ν
    have hh := hnear ρ
    change 1 < gaussianProbabilityLogLikelihood θ ((x, 1), ρ) -
      gaussianProbabilityLogLikelihood θ ((x, 1), μ) at hfail
    linarith

theorem gaussian_tiny_conclusions_of_notMem_failure {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} [Nonempty (Fin n)] (θ : Θ → Point d) (hθ : Continuous θ)
    (x : Fin n → Point d) (w : Fin n → ℝ) (R a : ℝ)
    (hgood : (x, w) ∉ gaussianTinyStructuralFailure θ R a) :
    (∀ i, |w i - 1| ≤ a) ∧ w ∈ positiveVectors n ∧
    ∃ μ : ProbabilityMeasure Θ, gaussianProbabilityOptimizerSet θ (x, w) = {μ} ∧
      (μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤ R ∧
      ∀ ν : ProbabilityMeasure Θ,
        gaussianProbabilityLogLikelihood θ ((x, 1), ν) - 1 ≤
          gaussianProbabilityLogLikelihood θ ((x, 1), μ) := by
  classical
  simp only [gaussianTinyStructuralFailure, mem_union, mem_setOf_eq, not_or] at hgood
  obtain ⟨⟨⟨hweight, hnonunique⟩, hsupport⟩, hgap⟩ := hgood
  have hw := not_not.mp hweight
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hfit := gaussianCanonicalFit_isMax x θ hθ w
  obtain ⟨μ, hμ⟩ := probabilityMixtureFiber_nonempty_of_mem_convexHull A hA
    (gaussianCanonicalFit x θ hθ w) hfit.1
  have hopt : μ ∈ gaussianProbabilityOptimizerSet θ (x, w) :=
    (gaussian_probability_optimizer_iff_score_fiber x θ hθ w _ hw.2 hfit μ).mpr hμ
  have huniq : ∀ ν ∈ gaussianProbabilityOptimizerSet θ (x, w), ν = μ := by
    intro ν hν
    by_contra hne
    exact hnonunique ⟨ν, μ, hν, hopt, hne⟩
  have hs : (μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤ R := by
    by_contra hbad
    exact hsupport ⟨μ, hopt, hbad⟩
  refine ⟨hw.1, hw.2, μ, ?_, hs.1, hs.2, ?_⟩
  · ext ν
    simp only [mem_singleton_iff]
    exact ⟨fun hν ↦ huniq ν hν, fun hν ↦ hν ▸ hopt⟩
  · intro ν
    have hle : gaussianOrdinaryLikelihoodGap θ ((x, w), (μ, ν)) ≤ 1 :=
      le_of_not_gt (fun h ↦ hgap ⟨(μ, ν), hopt, h⟩)
    change gaussianProbabilityLogLikelihood θ ((x, 1), ν) -
      gaussianProbabilityLogLikelihood θ ((x, 1), μ) ≤ 1 at hle
    linarith



end ReweightedNPMLE
end

/-! # Joint arbitrarily-small perturbations

The failure event quantifies over all probability laws, so the joint theorem
requires neither a chosen optimizer nor a data-dependent measurable selection.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Arbitrarily inverse-polynomially small perturbations, with uniqueness,
polylogarithmic finite support, and global Hellinger risk on one joint event. -/
theorem solution
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b L : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) (hL : 0 < L)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop, ∀ Gstar : ProbabilityMeasure K,
      ∃ G : Set (GaussianDataWeight d n), MeasurableSet G ∧
        (gaussianDataWeightMeasure Gstar n ((n : ℝ) ^ (2 * L + 2))).real Gᶜ ≤
          (4 * (d : ℝ) + 5) * (n : ℝ) ^ (-(b + 2)) ∧
        ∀ p ∈ G, (∀ i, |p.2 i - 1| ≤ (n : ℝ) ^ (-L)) ∧ p.2 ∈ positiveVectors n ∧
          ∃ μ : ProbabilityMeasure K,
            gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) p = {μ} ∧
            (μ : Measure K).support.Finite ∧ ((μ : Measure K).support.ncard : ℝ) ≤
              gaussianPaperSupportConstant d (8 * (2 * L + 6)) b *
                gaussianPaperAugmentedDimension d n ∧
            hellingerSq volume (compactGaussianMixtureDensity μ)
              (compactGaussianMixtureDensity Gstar) ≤
                gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d * Real.log n / n := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  letI : Nonempty K := hKnonempty.to_subtype
  let θ := fun a : K ↦ (a : Point d)
  have hθ : Continuous θ := continuous_subtype_val
  have hθbound : ∀ a : K, ‖θ a‖ ≤ S := fun a ↦ hKbound a.val a.property
  filter_upwards [gaussian_exact_regularization_conditional_tiny d hS hb hL θ hθ
      Subtype.val_injective hθbound,
    compactGaussianMixture_measurable_uniform_nearMLE_event hd K hKcompact hKnonempty hS hb hKbound,
    eventually_gaussianPaperAugmentedDimension_pos d,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    eventually_ge_atTop (1 : ℕ)] with n hcond hrisk hdim hlog hn
  intro Gstar
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  let P := compactGaussianSampleMeasure Gstar n
  let α := (n : ℝ) ^ (2 * L + 2)
  have hα : 0 < α := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  let Q := gammaProductMeasure n α α
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, gammaProductMeasure]
    letI : IsProbabilityMeasure (gammaMeasure α α) := isProbabilityMeasure_gammaMeasure hα hα
    infer_instance
  let E : Set (GaussianDataWeight d n) := gaussianTinyStructuralFailure θ
    (gaussianPaperSupportConstant d (8 * (2 * L + 6)) b * gaussianPaperAugmentedDimension d n)
    ((n : ℝ) ^ (-L))
  have hE : MeasurableSet E := measurableSet_gaussianTinyStructuralFailure θ hθ
    (by unfold gaussianPaperSupportConstant; positivity) _
  obtain ⟨X, hX, hnull, hcond⟩ := hcond
  let D := Xᶜ ∪ {x : Fin n → Point d | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖}
  have hrad : MeasurableSet {x : Fin n → Point d | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} := by
    have heq : {x : Fin n → Point d | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} =
        ⋃ i : Fin n, {x : Fin n → Point d | gaussianPaperSampleRadius d S b n < ‖x i‖} := by ext x; simp
    rw [heq]
    exact MeasurableSet.iUnion (fun i ↦ measurableSet_lt measurable_const
      ((continuous_apply i).norm.measurable))
  have hD : MeasurableSet D := hX.compl.union hrad
  have hXzero : P.real Xᶜ = 0 := by
    change ((compactGaussianSampleMeasure Gstar n) Xᶜ).toReal = 0
    rw [compactGaussianSampleMeasure_absolutelyContinuous Gstar n hnull, ENNReal.toReal_zero]
  have hDprob : P.real D ≤ (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) := by
    have h := measureReal_union_le (μ := P) Xᶜ {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖}
    rw [hXzero, zero_add] at h
    exact h.trans (compactGaussianSampleMeasure_paper_radius_tail Gstar hS hb hKbound hlog hn)
  have hsections : ∀ x ∉ D, Q.real (Prod.mk x ⁻¹' E) ≤ 3 * (n : ℝ) ^ (-(b + 2)) := by
    intro x hx
    have hxX : x ∈ X := by
      by_contra h
      exact hx (Or.inl h)
    have hxrad : ∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n := by
      intro i
      by_contra h
      exact hx (Or.inr ⟨i, lt_of_not_ge h⟩)
    obtain ⟨H, hH, hHprob, hgood⟩ := hcond x hxX hxrad
    apply le_trans (measureReal_mono (μ := Q) (s₂ := Hᶜ) ?_) hHprob
    intro w hw
    by_contra hwH
    obtain ⟨hcoord, hwpos, μ, huniq, hfinite, hcard, hnear⟩ := hgood w (not_not.mp hwH)
    exact notMem_gaussianTinyStructuralFailure_of_unique_nearMLE θ x w _ _ hcoord hwpos
      μ huniq hfinite hcard hnear hw
  have hEprob : (P.prod Q).real E ≤ (2 * (d : ℝ) + 4) * (n : ℝ) ^ (-(b + 2)) := by
    have h := measureReal_prod_le_of_uniform_section_bound P Q E hE D hD
      (show 0 ≤ 3 * (n : ℝ) ^ (-(b + 2)) by positivity) hsections
    exact h.trans (by linarith)
  obtain ⟨N, hN, hNprob, hNgood⟩ := hrisk Gstar
  refine ⟨(E ∪ (N ×ˢ univ))ᶜ, (hE.union (hN.prod MeasurableSet.univ)).compl, ?_, ?_⟩
  · simp only [compl_compl]
    have hNprod : (P.prod Q).real (N ×ˢ univ) = P.real N := by simp
    have h := measureReal_union_le (μ := P.prod Q) E (N ×ˢ univ)
    rw [hNprod] at h
    exact h.trans (by linarith)
  · intro p hp
    have hpE : p ∉ E := fun h ↦ hp (Or.inl h)
    have hpN : p.1 ∉ N := fun h ↦ hp (Or.inr ⟨h, mem_univ _⟩)
    obtain ⟨hcoord, hpos, μ, huniq, hfinite, hcard, hnear⟩ :=
      gaussian_tiny_conclusions_of_notMem_failure θ hθ p.1 p.2 _ _ hpE
    refine ⟨hcoord, hpos, μ, huniq, hfinite, hcard, ?_⟩
    have hh := hnear Gstar
    rw [gaussianProbabilityLogLikelihood_one, gaussianProbabilityLogLikelihood_one] at hh
    exact hNgood p.1 hpN μ hh
