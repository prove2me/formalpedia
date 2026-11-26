-- Prove2me | solution 1 for ReweightedNPMLE.gaussian_optimizer_fiber_unique_of_evaluation_independence
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:17:20.346612+00:00
-- url     : https://prove2.me/submissions/c48b5c2f-d7e7-4a8e-a5bf-af2b75bab1f2

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
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
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
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
import Definitions.Def_ReweightedNPMLE_GaussianStructural
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureFiber_eq_singleton_of_small_extreme_supports

-- Inline helpers preserved from ReweightedNPMLE.Gaussian.
section
/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE































/-- The Gaussian translation identity used in Sections 3 and 4 of the manuscript. -/
theorem gaussianKernel_eq_density_mul_exp_score {d : ℕ} (x θ : Point d) :
    gaussianKernel d x θ = gaussianDensity d x * Real.exp (gaussianScore x θ) := by
  rw [gaussianKernel, gaussianDensity, gaussianScore, mul_assoc, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real]
  ring































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianStructural.
section
/-!
# Gaussian dictionary links for full-measure structural bounds

The canceled Gaussian score dictionary has the same optimizer fibers as the
Gaussian density dictionary. Its relative fitted hull is the convex hull of
the relative atoms used in the verified Taylor-width estimate.
-/

open Set MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE





theorem probabilityMixtureValue_coordinate_scale {Θ : Type*}
    [MeasurableSpace Θ] {n : ℕ} (A : Θ → Fin n → ℝ)
    (c : Fin n → ℝ) (μ : ProbabilityMeasure Θ) :
    probabilityMixtureValue (fun θ i ↦ c i * A θ i) μ = c * probabilityMixtureValue A μ := by
  funext i
  exact integral_const_mul (c i) (fun θ ↦ A θ i)

theorem probabilityMixtureFiber_coordinate_scale {Θ : Type*}
    [MeasurableSpace Θ] {n : ℕ} (A : Θ → Fin n → ℝ)
    (c v : Fin n → ℝ) (hc : ∀ i, c i ≠ 0) :
    probabilityMixtureFiber (fun θ i ↦ c i * A θ i) (c * v) = probabilityMixtureFiber A v := by
  ext μ
  change probabilityMixtureValue (fun θ i ↦ c i * A θ i) μ = c * v ↔
    probabilityMixtureValue A μ = v
  rw [probabilityMixtureValue_coordinate_scale]
  constructor
  · intro h
    funext i
    exact mul_left_cancel₀ (hc i) (congrFun h i)
  · intro h
    rw [h]

theorem isExtremeProbabilityMixture_coordinate_scale {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (c v : Fin n → ℝ) (hc : ∀ i, c i ≠ 0)
    (μ : ProbabilityMeasure Θ) :
    IsExtremeProbabilityMixture (fun θ i ↦ c i * A θ i) (c * v) μ ↔
      IsExtremeProbabilityMixture A v μ := by
  unfold IsExtremeProbabilityMixture probabilityFiberImage
  rw [probabilityMixtureFiber_coordinate_scale A c v hc]

theorem gaussian_probability_optimizer_fiber_eq_score {Θ : Type*}
    [MeasurableSpace Θ] {d n : ℕ} (x : Fin n → Point d)
    (θ : Θ → Point d) (v : Fin n → ℝ) :
    probabilityMixtureFiber (fun a i ↦ gaussianKernel d (x i) (θ a))
      ((fun i ↦ gaussianDensity d (x i)) * v) =
        probabilityMixtureFiber (fun a ↦ gaussianScoreFeature x (θ a)) v := by
  have heq : (fun a i ↦ gaussianKernel d (x i) (θ a)) =
      (fun a i ↦ gaussianDensity d (x i) * gaussianScoreFeature x (θ a) i) := by
    funext a i
    exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
  rw [heq]
  exact probabilityMixtureFiber_coordinate_scale _ _ _
    (fun i ↦ (gaussianDensity_pos d (x i)).ne')







end ReweightedNPMLE
end

/-!
# Gaussian dictionary links for full-measure structural bounds

The canceled Gaussian score dictionary has the same optimizer fibers as the
Gaussian density dictionary. Its relative fitted hull is the convex hull of
the relative atoms used in the verified Taylor-width estimate.
-/

open Set MeasureTheory
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The Gaussian uniqueness consequence of simultaneous evaluation
independence. The independence assumption has exactly the paper's threshold,
and includes data-dependent atom locations. Its almost-everywhere validity is
the separate analytic incidence theorem, not an assumption hidden here. -/
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n m : ℕ} [Nonempty (Fin n)] (x : Fin n → Point d)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθinj : Function.Injective θ)
    (w v : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (hvmax : IsMaxOn (convexHull ℝ (range (fun a ↦ gaussianScoreFeature x (θ a))))
      (weightedLogLikelihood w) v)
    (hsize : (2 * m) * (d + 1) ≤ n)
    (hgeneric : ∀ k : ℕ, k * (d + 1) ≤ n → ∀ t : Fin k → Point d,
      Function.Injective t → LinearIndependent ℝ (fun j i ↦ gaussianKernel d (x i) (t j)))
    (hsmall : ∀ μ : ProbabilityMeasure Θ,
      IsExtremeProbabilityMixture (fun a ↦ gaussianScoreFeature x (θ a)) v μ →
        (μ : Measure Θ).support.ncard ≤ m) :
    ∃ μ : ProbabilityMeasure Θ,
      probabilityMixtureFiber (fun a i ↦ gaussianKernel d (x i) (θ a))
        ((fun i ↦ gaussianDensity d (x i)) * v) = {μ} ∧
      IsExtremeProbabilityMixture (fun a i ↦ gaussianKernel d (x i) (θ a))
        ((fun i ↦ gaussianDensity d (x i)) * v) μ ∧
      (μ : Measure Θ).support.Finite ∧ (μ : Measure Θ).support.ncard ≤ m := by
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hCpos : convexHull ℝ (range A) ⊆ positiveVectors n :=
    convexHull_min (by rintro a ⟨b, rfl⟩; exact fun i ↦ Real.exp_pos _)
      (convex_positiveVectors n)
  have hind : ∀ k : ℕ, k ≤ 2 * m → ∀ t : Fin k → Θ,
      Function.Injective t → LinearIndependent ℝ (A ∘ t) := by
    intro k hk t ht
    have hkt : k * (d + 1) ≤ n := (Nat.mul_le_mul_right (d + 1) hk).trans hsize
    have hlin := hgeneric k hkt (θ ∘ t) (hθinj.comp ht)
    let S : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      { toFun := fun u i ↦ gaussianDensity d (x i) * u i
        map_add' := by intro u z; funext i; exact mul_add _ _ _
        map_smul' := by
          intro a u
          funext i
          change gaussianDensity d (x i) * (a * u i) = a * (gaussianDensity d (x i) * u i)
          ring }
    have heq : S ∘ (A ∘ t) = (fun j i ↦ gaussianKernel d (x i) (θ (t j))) := by
      funext j i
      exact (gaussianKernel_eq_density_mul_exp_score (x i) (θ (t j))).symm
    apply LinearIndependent.of_comp S
    rw [heq]
    exact hlin
  obtain ⟨μ, hfiber, hext, hfinite, hcard⟩ :=
    probabilityMixtureFiber_eq_singleton_of_small_extreme_supports A hA
      (convex_convexHull ℝ (range A)) hCpos (subset_convexHull ℝ _)
      w v hw hvmax hvmax.1 (L := 2 * m) le_rfl hind hsmall
  refine ⟨μ, ?_, ?_, hfinite, hcard⟩
  · rw [gaussian_probability_optimizer_fiber_eq_score]
    exact hfiber
  · have heq : (fun a i ↦ gaussianKernel d (x i) (θ a)) =
        (fun a i ↦ gaussianDensity d (x i) * A a i) := by
      funext a i
      exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
    rw [heq]
    exact (isExtremeProbabilityMixture_coordinate_scale A _ v
      (fun i ↦ (gaussianDensity_pos d (x i)).ne') μ).mpr hext
