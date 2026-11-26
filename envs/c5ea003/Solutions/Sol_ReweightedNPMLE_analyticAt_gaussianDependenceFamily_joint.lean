-- Prove2me | solution 1 for ReweightedNPMLE.analyticAt_gaussianDependenceFamily_joint
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:53:28.314379+00:00
-- url     : https://prove2.me/submissions/33d44d1e-ced8-4ea3-a5ab-3f6a1108bf77

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianIncidence
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_analyticAt_gaussianKernel_joint

-- Inline helpers preserved from ReweightedNPMLE.GaussianIncidence.
section
/-!
# Nontrivial Gaussian families for the generic incidence argument

Distinct Gaussian translates are linearly independent as functions on the
whole observation space. This is proved using Gaussian mixture identifiability
and a positive finite-probability perturbation, so no choice of a separating
direction or Vandermonde derivative calculation is required.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE











theorem analyticAt_finiteGaussianMixture_parameter {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d k : ℕ}
    (θ : Fin k → E → Point d) (c : Fin k → E → ℝ) (y : E → Point d) (e : E)
    (hθ : ∀ j, AnalyticAt ℝ (θ j) e) (hc : ∀ j, AnalyticAt ℝ (c j) e)
    (hy : AnalyticAt ℝ y e) :
    AnalyticAt ℝ (fun a ↦ finiteGaussianMixture (fun j ↦ c j a) (fun j ↦ θ j a) (y a)) e := by
  unfold finiteGaussianMixture
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (hc j).mul ((analyticAt_gaussianKernel_joint (y e, θ j e)).comp
    (f := fun a ↦ (y a, θ j a)) (hy.prod (hθ j)))



























end ReweightedNPMLE
end

/-!
# Nontrivial Gaussian families for the generic incidence argument

Distinct Gaussian translates are linearly independent as functions on the
whole observation space. This is proved using Gaussian mixture identifiability
and a positive finite-probability perturbation, so no choice of a separating
direction or Vandermonde derivative calculation is required.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {d k : ℕ} (j₀ : Fin k)
    (z : GaussianDependenceParameter d k j₀ × Point d) :
    AnalyticAt ℝ (fun p ↦ gaussianDependenceFamily j₀ p.1 p.2) z := by
  have hloc : AnalyticAt ℝ
      (fun p : GaussianDependenceParameter d k j₀ × Point d ↦ p.1.1) z :=
    (analyticAt_fst : AnalyticAt ℝ
      (fun η : GaussianDependenceParameter d k j₀ ↦ η.1) z.1).comp
        (f := fun p : GaussianDependenceParameter d k j₀ × Point d ↦ p.1) analyticAt_fst
  have hcoef : AnalyticAt ℝ
      (fun p : GaussianDependenceParameter d k j₀ × Point d ↦ p.1.2) z :=
    (analyticAt_snd : AnalyticAt ℝ
      (fun η : GaussianDependenceParameter d k j₀ ↦ η.2) z.1).comp
        (f := fun p : GaussianDependenceParameter d k j₀ × Point d ↦ p.1) analyticAt_fst
  unfold gaussianDependenceFamily
  apply analyticAt_finiteGaussianMixture_parameter
  · intro j
    exact ((ContinuousLinearMap.proj j : (Fin k → Point d) →L[ℝ] Point d).analyticAt z.1.1).comp
      (f := fun p : GaussianDependenceParameter d k j₀ × Point d ↦ p.1.1) hloc
  · intro j
    by_cases hj : j = j₀
    · simp only [normalizedGaussianCoefficients, dif_pos hj]
      exact analyticAt_const
    · simp only [normalizedGaussianCoefficients, dif_neg hj]
      exact ((ContinuousLinearMap.proj ⟨j, hj⟩ :
        ({j : Fin k // j ≠ j₀} → ℝ) →L[ℝ] ℝ).analyticAt z.1.2).comp
        (f := fun p : GaussianDependenceParameter d k j₀ × Point d ↦ p.1.2) hcoef
  · exact analyticAt_snd
