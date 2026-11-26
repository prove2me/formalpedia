-- Prove2me | solution 1 for ReweightedNPMLE.compactGaussianMixture_uniform_nearMLE_bad_event_bound_explicit_tuned
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:16:09.855107+00:00
-- url     : https://prove2.me/submissions/432a8daa-685f-4bc9-98a0-5caa7a18a201

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianNearMLE
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_compactGaussianMixture_uniform_nearMLE_bad_event_bound_explicit

/-!
# Uniform near-MLE control for compact Gaussian mixtures

This module closes the main interface between the analytic Gaussian-mixture
net and the finite likelihood-ratio test.  Candidates are genuine bundled
probability measures on a compact location set, rather than a finite-mixture
surrogate parameterization.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The fully explicit radius theorem with the likelihood-test threshold
chosen as `t = sqrt (2A/n)`.  The squared-Hellinger cutoff becomes
`2·globalSq + 4A/n`, and the finite-net failure factor becomes
`cardBound · exp (1-A)`. -/
theorem solution
    {d L M n : ℕ} (hn : 0 < n)
    (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S ε r A : ℝ} (hS : 0 ≤ S) (hε : 0 < ε) (hr : 0 < r)
    (hA : 0 ≤ A)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S)
    (hM : 0 < M)
    (hrelativeHalf : gaussianMomentRelativeError
      (S + Real.sqrt d * r) S L ≤ 1 / 2)
    (hweightSmall : Real.exp
      (2 * ((S + Real.sqrt d * r) * S + S ^ 2 / 2)) *
        (2 * gaussianMomentDimension d L / M) ≤ 1 / 2)
    (Gstar : ProbabilityMeasure K)
    (hnδ : (n : ℝ) * gaussianNetLogError d L M
      (S + Real.sqrt d * r) S ε ≤ 1) :
    (Measure.pi (fun _ : Fin n ↦ volume.withDensity (fun y ↦
      ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))).real
        {x | ∃ G : ProbabilityMeasure K,
          (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
              ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
          2 * gaussianNetHellingerSqError d L M S ε +
              4 * A / n <
            hellingerSq volume (compactGaussianMixtureDensity G)
              (compactGaussianMixtureDensity Gstar)} ≤
      2 * n * d * Real.exp (-r ^ 2 / 2) +
        (((boundedLocationCellCount d S ε) ^ d) ^
            (gaussianMomentDimension d L + 1) * (M + 1) ^
              gaussianMomentDimension d L) * Real.exp (1 - A) := by
  let t : ℝ := Real.sqrt (2 * A / n)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have harg : 0 ≤ 2 * A / (n : ℝ) := by positivity
  have htSq : t ^ 2 = 2 * A / n := by
    exact Real.sq_sqrt harg
  have hmain :=
    compactGaussianMixture_uniform_nearMLE_bad_event_bound_explicit
      K hKcompact hKnonempty hS hε hr hKbound hM
      hrelativeHalf hweightSmall Gstar t hnδ
  simpa only [htSq, show 2 * (2 * A / (n : ℝ)) = 4 * A / n by ring,
    show 1 - (n : ℝ) * (2 * A / n) / 2 = 1 - A by
      field_simp] using hmain
