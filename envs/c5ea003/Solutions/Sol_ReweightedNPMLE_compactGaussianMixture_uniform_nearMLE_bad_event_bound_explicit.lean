-- Prove2me | solution 1 for ReweightedNPMLE.compactGaussianMixture_uniform_nearMLE_bad_event_bound_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:15:12.654713+00:00
-- url     : https://prove2.me/submissions/54087f9c-426b-4348-8570-a811c83f5d78

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
import Theorems.Thm_ReweightedNPMLE_compactGaussianMixture_uniform_nearMLE_bad_event_bound_bounded
import Theorems.Thm_ReweightedNPMLE_gaussianLocationMixtureSample_max_radius_tail

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
/-- Fully explicit radius specialization of
`compactGaussianMixture_uniform_nearMLE_bad_event_bound`.  The sample-radius
failure term is discharged under the true compact Gaussian mixture law and
is `2 n d exp (-r²/2)`. -/
theorem solution
    {d L M n : ℕ}
    (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S ε r : ℝ} (hS : 0 ≤ S) (hε : 0 < ε) (hr : 0 < r)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S)
    (hM : 0 < M)
    (hrelativeHalf : gaussianMomentRelativeError
      (S + Real.sqrt d * r) S L ≤ 1 / 2)
    (hweightSmall : Real.exp
      (2 * ((S + Real.sqrt d * r) * S + S ^ 2 / 2)) *
        (2 * gaussianMomentDimension d L / M) ≤ 1 / 2)
    (Gstar : ProbabilityMeasure K) (t : ℝ)
    (hnδ : (n : ℝ) * gaussianNetLogError d L M
      (S + Real.sqrt d * r) S ε ≤ 1) :
    (Measure.pi (fun _ : Fin n ↦ volume.withDensity (fun y ↦
      ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))).real
        {x | ∃ G : ProbabilityMeasure K,
          (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
              ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
          2 * gaussianNetHellingerSqError d L M S ε + 2 * t ^ 2 <
            hellingerSq volume (compactGaussianMixtureDensity G)
              (compactGaussianMixtureDensity Gstar)} ≤
      2 * n * d * Real.exp (-r ^ 2 / 2) +
        (((boundedLocationCellCount d S ε) ^ d) ^
            (gaussianMomentDimension d L + 1) * (M + 1) ^
              gaussianMomentDimension d L) *
          Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by
  let R : ℝ := S + Real.sqrt d * r
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have htail := gaussianLocationMixtureSample_max_radius_tail
    (n := n) (Gstar : Measure K) (fun θ : K ↦ (θ : Point d))
    measurable_subtype_coe (S := S) (t := r)
    (fun θ ↦ hKbound θ θ.property) hr
  rw [gaussianLocationMixtureLaw_eq_withDensity_gaussianMixture
    (Gstar : Measure K) (fun θ : K ↦ (θ : Point d))
      measurable_subtype_coe] at htail
  have hbad : ({x : Fin n → Point d | ∀ i, x i ∈
      {y : Point d | ‖y‖ ≤ R}}ᶜ) =
      {x : Fin n → Point d | ∃ i, ‖x i‖ > R} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    push Not
    rfl
  have hradius :
      (Measure.pi (fun _ : Fin n ↦ volume.withDensity (fun y ↦
        ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))).real
          ({x : Fin n → Point d | ∀ i, x i ∈
            {y : Point d | ‖y‖ ≤ R}}ᶜ) ≤
        2 * n * d * Real.exp (-r ^ 2 / 2) := by
    rw [hbad]
    simpa only [compactGaussianMixtureDensity, R] using htail
  simpa only [R] using
    (compactGaussianMixture_uniform_nearMLE_bad_event_bound_bounded
      K {x : Point d | ‖x‖ ≤ R} hKcompact hKnonempty
      hR hS hε hKbound (fun x hx ↦ hx) hM hrelativeHalf hweightSmall
      Gstar t (2 * n * d * Real.exp (-r ^ 2 / 2)) hnδ hradius)
