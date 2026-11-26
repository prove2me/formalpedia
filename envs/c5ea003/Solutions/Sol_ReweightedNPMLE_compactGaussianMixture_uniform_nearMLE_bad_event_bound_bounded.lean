-- Prove2me | solution 1 for ReweightedNPMLE.compactGaussianMixture_uniform_nearMLE_bad_event_bound_bounded
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:14:27.38179+00:00
-- url     : https://prove2.me/submissions/8b642a5b-2074-496c-acb7-292618fb4094

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
import Theorems.Thm_ReweightedNPMLE_compactGaussianMixture_uniform_nearMLE_bad_event_bound_of_cover
import Theorems.Thm_ReweightedNPMLE_norm_sub_lt_of_boundedLocationCellCode_eq

-- Inline helpers preserved from ReweightedNPMLE.EuclideanLocationNet.
section
/-!
# Explicit finite nets for bounded Euclidean sets

This module implements the coordinate-cell construction used in the paper's
entropy argument.  A set contained in the radius-`S` Euclidean ball is split
into cells of coordinate width `ε / (d + 2)`.  Choosing one point of the set
from each occupied cell gives an internal `ε`-net with an explicit cardinality
bound.
-/

open scoped BigOperators

namespace ReweightedNPMLE



















theorem boundedLocationRepresentative_code {d : ℕ} {K : Set (Point d)}
    (hKnonempty : K.Nonempty) {S ε : ℝ} (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (u : K) :
    boundedLocationCellCode S ε hε hKbound
        (boundedLocationRepresentative K hKnonempty S ε hε hKbound
          (boundedLocationCellCode S ε hε hKbound u)) =
      boundedLocationCellCode S ε hε hKbound u := by
  let h : ∃ v : K, boundedLocationCellCode S ε hε hKbound v =
      boundedLocationCellCode S ε hε hKbound u := ⟨u, rfl⟩
  rw [boundedLocationRepresentative, dif_pos h]
  exact h.choose_spec



theorem boundedLocationNet_subset {d : ℕ} (K : Set (Point d))
    (hKnonempty : K.Nonempty) {S ε : ℝ} (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ↑(boundedLocationNet K hKnonempty S ε hε hKbound) ⊆ K := by
  classical
  intro u hu
  rw [Finset.mem_coe, boundedLocationNet, Finset.mem_image] at hu
  rcases hu with ⟨c, _hc, rfl⟩
  exact (boundedLocationRepresentative K hKnonempty S ε hε hKbound c).property

/-- Explicit polynomial cardinality bound for the internal location net. -/
theorem card_boundedLocationNet_le {d : ℕ} (K : Set (Point d))
    (hKnonempty : K.Nonempty) {S ε : ℝ} (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    (boundedLocationNet K hKnonempty S ε hε hKbound).card ≤
      (boundedLocationCellCount d S ε) ^ d := by
  classical
  calc
    (boundedLocationNet K hKnonempty S ε hε hKbound).card ≤
        (Finset.univ : Finset
          (Fin d → Fin (boundedLocationCellCount d S ε))).card := by
      exact Finset.card_image_le
    _ = (boundedLocationCellCount d S ε) ^ d := by simp

/-- Every point of `K` is within `ε` of a point of the explicit internal net. -/
theorem exists_mem_boundedLocationNet_norm_sub_le {d : ℕ}
    (K : Set (Point d)) (hKnonempty : K.Nonempty)
    {S ε : ℝ} (hε : 0 < ε) (hKbound : ∀ u ∈ K, ‖u‖ ≤ S)
    (u : Point d) (hu : u ∈ K) :
    ∃ v ∈ boundedLocationNet K hKnonempty S ε hε hKbound,
      ‖u - v‖ ≤ ε := by
  classical
  let uK : K := ⟨u, hu⟩
  let c := boundedLocationCellCode S ε hε hKbound uK
  let vK := boundedLocationRepresentative K hKnonempty S ε hε hKbound c
  refine ⟨(vK : Point d), ?_, ?_⟩
  · rw [boundedLocationNet, Finset.mem_image]
    exact ⟨c, Finset.mem_univ c, rfl⟩
  · exact (norm_sub_lt_of_boundedLocationCellCode_eq hε hKbound uK vK
      (boundedLocationRepresentative_code hKnonempty hε hKbound uK).symm).le

end ReweightedNPMLE
end

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
/-- Uniform near-MLE control with the coordinate-cell location entropy made
fully explicit. -/
theorem solution
    {d L M n : ℕ}
    (K X : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (hXbound : ∀ x ∈ X, ‖x‖ ≤ T)
    (hM : 0 < M)
    (hrelativeHalf : gaussianMomentRelativeError T S L ≤ 1 / 2)
    (hweightSmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      (2 * gaussianMomentDimension d L / M) ≤ 1 / 2)
    (Gstar : ProbabilityMeasure K) (t radiusBound : ℝ)
    (hnδ : (n : ℝ) * gaussianNetLogError d L M T S ε ≤ 1)
    (hradius :
      (Measure.pi (fun _ : Fin n ↦ volume.withDensity (fun y ↦
        ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))).real
          ({x : Fin n → Point d | ∀ i, x i ∈ X}ᶜ) ≤ radiusBound) :
    (Measure.pi (fun _ : Fin n ↦ volume.withDensity (fun y ↦
      ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))).real
        {x | ∃ G : ProbabilityMeasure K,
          (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
              ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
          2 * gaussianNetHellingerSqError d L M S ε + 2 * t ^ 2 <
            hellingerSq volume (compactGaussianMixtureDensity G)
              (compactGaussianMixtureDensity Gstar)} ≤
      radiusBound +
        (((boundedLocationCellCount d S ε) ^ d) ^
            (gaussianMomentDimension d L + 1) * (M + 1) ^
              gaussianMomentDimension d L) *
          Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by
  let Q := boundedLocationNet K hKnonempty S ε hε hKbound
  have hmain := compactGaussianMixture_uniform_nearMLE_bad_event_bound_of_cover
    K X Q hKcompact hKnonempty hT hS hε hKbound hXbound
    (boundedLocationNet_subset K hKnonempty hε hKbound)
    (exists_mem_boundedLocationNet_norm_sub_le K hKnonempty hε hKbound)
    hM hrelativeHalf hweightSmall Gstar t radiusBound hnδ hradius
  refine hmain.trans (add_le_add_right ?_ radiusBound)
  have hcard : Q.card ≤ (boundedLocationCellCount d S ε) ^ d := by
    exact card_boundedLocationNet_le K hKnonempty hε hKbound
  have hcardReal : (Q.card : ℝ) ≤
      ((boundedLocationCellCount d S ε) ^ d : ℕ) := by
    exact_mod_cast hcard
  have hcardReal' : (Q.card : ℝ) ≤
      (boundedLocationCellCount d S ε : ℝ) ^ d := by
    simpa only [Nat.cast_pow] using hcardReal
  gcongr
