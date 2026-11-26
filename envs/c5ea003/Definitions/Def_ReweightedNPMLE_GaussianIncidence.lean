-- Prove2me | Definitions.Def_ReweightedNPMLE_GaussianIncidence
-- name    : ReweightedNPMLE_GaussianIncidence
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:25:24.178016+00:00
-- url     : https://prove2.me/theorems/ab16064c-5dd2-4cbe-bbd0-d77d48fdd1b6
-- title:
--   Normalized charts for signed Gaussian linear dependences
-- statement:
--   Fix a number of locations \(k\) and a distinguished index \(j_0\). A dependence parameter consists of locations \((\theta_1,\ldots,\theta_k)\in(\mathbb R^d)^k\) and real coefficients \(b_j\) for \(j\ne j_0\). Define normalized coefficients by \(c_{j_0}=1\) and \(c_j=b_j\) otherwise. The dependence domain requires the locations to be pairwise distinct. Its associated function is the signed Gaussian sum
--   \[
--   F_{\theta,b}(y)=\sum_{j=1}^k c_j(2\pi)^{-d/2}e^{-\|y-\theta_j\|^2/2}.
--   \]
--   The coefficients need not be nonnegative or sum to one. Fixing one coefficient to one gives a chart for nontrivial linear dependences without a redundant overall coefficient scale.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianIncidence.lean#L159-L173

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
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

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

















/-- A coefficient chart has all location coordinates but omits the normalized
coefficient at `j₀`. -/
abbrev GaussianDependenceParameter (d k : ℕ) (j₀ : Fin k) :=
  (Fin k → Point d) × ({j : Fin k // j ≠ j₀} → ℝ)

noncomputable def normalizedGaussianCoefficients {k : ℕ} (j₀ : Fin k)
    (b : {j : Fin k // j ≠ j₀} → ℝ) : Fin k → ℝ :=
  fun j ↦ if hj : j = j₀ then 1 else b ⟨j, hj⟩

def gaussianDependenceDomain {d k : ℕ} (j₀ : Fin k) :
    Set (GaussianDependenceParameter d k j₀) := {η | Function.Injective η.1}

noncomputable def gaussianDependenceFamily {d k : ℕ} (j₀ : Fin k)
    (η : GaussianDependenceParameter d k j₀) (y : Point d) : ℝ :=
  finiteGaussianMixture (normalizedGaussianCoefficients j₀ η.2) η.1 y















end ReweightedNPMLE


