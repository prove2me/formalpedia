-- Prove2me | solution 1 for ReweightedNPMLE.exists_mem_finiteGaussianMixtureGrid_simultaneous_approximation_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:12:31.521801+00:00
-- url     : https://prove2.me/submissions/becd2506-e35b-45ea-bc88-06bdba9c41e3

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_abs_log_rounded_finiteGaussianMixture_sub_gaussianMixture_le
import Theorems.Thm_ReweightedNPMLE_exists_finite_gaussianMixture_simultaneous_approximation
import Theorems.Thm_ReweightedNPMLE_hellingerSq_gaussianMixture_finite_rounding_le
import Theorems.Thm_ReweightedNPMLE_simplexGridRound_mem_simplexWeightGrid
import Theorems.Thm_ReweightedNPMLE_simplexGridRound_nonneg
import Theorems.Thm_ReweightedNPMLE_sum_abs_simplexGridRound_sub_le
import Theorems.Thm_ReweightedNPMLE_sum_simplexGridRound

-- Inline helpers preserved from ReweightedNPMLE.SimplexGrid.
section
/-!
# Finite simplex-grid rounding

The deterministic denominator-grid construction used to discretize the
Carathéodory mixture weights in the likelihood net.
-/

open scoped BigOperators

namespace ReweightedNPMLE





































theorem mem_validSimplexWeightGrid_iff {k M : ℕ}
    {w : Fin (k + 1) → ℝ} :
    w ∈ validSimplexWeightGrid k M ↔
      w ∈ simplexWeightGrid k M ∧ ∀ i, 0 ≤ w i := by
  simp [validSimplexWeightGrid]









theorem simplexGridRound_mem_validSimplexWeightGrid {k M : ℕ}
    (hM : 0 < M) (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1) :
    simplexGridRound k M w ∈ validSimplexWeightGrid k M := by
  rw [mem_validSimplexWeightGrid_iff]
  exact ⟨simplexGridRound_mem_simplexWeightGrid w hw hwsum,
    simplexGridRound_nonneg hM w hw hwsum⟩

end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianFiniteNet.
section
/-!
# Finite Gaussian-mixture grids

This module combines a finite location set with the denominator simplex grid.
It produces an actual finite set of Gaussian-mixture densities, proves the
entropy count used in the likelihood-net argument, and packages the local
log-density and global Hellinger rounding estimates for members of that set.
-/

open scoped BigOperators
open MeasureTheory

namespace ReweightedNPMLE

























/-- Any mixture using locations from `Q` and a valid grid weight belongs to
the finite mixture grid. -/
theorem finiteGaussianMixture_mem_grid {d k M : ℕ}
    (Q : Finset (Point d)) (v : Fin (k + 1) → ℝ)
    (η : Fin (k + 1) → Point d)
    (hv : v ∈ validSimplexWeightGrid k M)
    (hη : ∀ i, η i ∈ Q) :
    finiteGaussianMixture v η ∈ finiteGaussianMixtureGrid d k M Q := by
  classical
  let z : Fin (k + 1) → Q := fun i ↦ ⟨η i, hη i⟩
  rw [finiteGaussianMixtureGrid, Finset.mem_image]
  refine ⟨(z, v), Finset.mem_product.mpr ⟨Finset.mem_univ z, hv⟩, ?_⟩
  congr









/-- Coordinatewise location rounding followed by denominator rounding of the
weights lands in the finite Gaussian-mixture grid. -/
theorem finiteGaussianMixture_rounding_mem_grid {d k M : ℕ}
    (hM : 0 < M) (Q : Finset (Point d))
    (w : Fin (k + 1) → ℝ) (η : Fin (k + 1) → Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hη : ∀ i, η i ∈ Q) :
    finiteGaussianMixture (simplexGridRound k M w) η ∈
      finiteGaussianMixtureGrid d k M Q :=
  finiteGaussianMixture_mem_grid Q _ η
    (simplexGridRound_mem_validSimplexWeightGrid hM w hw hwsum) hη











end ReweightedNPMLE
end

/-!
# Finite Gaussian-mixture grids

This module combines a finite location set with the denominator simplex grid.
It produces an actual finite set of Gaussian-mixture densities, proves the
entropy count used in the likelihood-net argument, and packages the local
log-density and global Hellinger rounding estimates for members of that set.
-/

open scoped BigOperators
open MeasureTheory

open ReweightedNPMLE
open ReweightedNPMLE in
/-- End-to-end deterministic finite-net theorem for a supplied finite internal
location cover.  An arbitrary compactly supported mixing law is first
replaced by a simultaneous moment-matched finite mixture, then its locations
and weights are rounded into one concrete member of the finite Gaussian-
mixture grid. -/
theorem solution
    {d L M : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (K X : Set (Point d)) (Q : Finset (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hϑK : ∀ a, ϑ a ∈ K)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (hXbound : ∀ x ∈ X, ‖x‖ ≤ T)
    (hQK : ↑Q ⊆ K)
    (hQcover : ∀ u ∈ K, ∃ v ∈ Q, ‖u - v‖ ≤ ε)
    (hM : 0 < M)
    (hrelativeHalf : gaussianMomentRelativeError T S L ≤ 1 / 2)
    (hweightSmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      (2 * gaussianMomentDimension d L / M) ≤ 1 / 2) :
    ∃ p ∈ finiteGaussianMixtureGrid d (gaussianMomentDimension d L) M Q,
      hellingerSq volume (gaussianMixture μ ϑ) p ≤
          2 * gaussianMomentHellingerError S L + ε ^ 2 +
            4 * (2 * gaussianMomentDimension d L / M) ∧
      ∀ x ∈ X,
        |Real.log (p x) - Real.log (gaussianMixture μ ϑ x)| ≤
          (T + S) * ε +
            2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
              (2 * gaussianMomentDimension d L / M) +
            2 * gaussianMomentRelativeError T S L := by
  obtain ⟨w, z, hw, hzK, hglobal0, hrelative0⟩ :=
    exists_finite_gaussianMixture_simultaneous_approximation
      μ ϑ hϑmeas K X hKcompact hKnonempty hϑK hT hS hKbound hXbound
  have hchoice : ∀ i, ∃ η ∈ Q, ‖z i - η‖ ≤ ε := by
    intro i
    exact hQcover (z i) (hzK i)
  choose η hηQ hθη using hchoice
  have hηK : ∀ i, η i ∈ K := fun i ↦ hQK (hηQ i)
  let v := simplexGridRound (gaussianMomentDimension d L) M w
  have hvnonneg : ∀ i, 0 ≤ v i :=
    simplexGridRound_nonneg hM w hw.1 hw.2
  have hvsum : ∑ i, v i = 1 := sum_simplexGridRound w
  have hl1vw : ∑ i, |v i - w i| ≤
      2 * gaussianMomentDimension d L / M :=
    sum_abs_simplexGridRound_sub_le hM w hw.1 hw.2
  have hl1wv : ∑ i, |w i - v i| ≤
      2 * gaussianMomentDimension d L / M := by
    simpa only [abs_sub_comm] using hl1vw
  refine ⟨finiteGaussianMixture v η,
    finiteGaussianMixture_rounding_mem_grid hM Q w η hw.1 hw.2 hηQ,
    ?_, ?_⟩
  · have hglobal : hellingerSq volume (gaussianMixture μ ϑ)
        (finiteGaussianMixture w z) ≤ gaussianMomentHellingerError S L := by
      simpa only [gaussianMomentHellingerError] using hglobal0
    have hround := hellingerSq_gaussianMixture_finite_rounding_le
      μ ϑ hϑmeas w v z η hw.1 hvnonneg hw.2 hvsum hε.le hθη hglobal
    have hmass : 4 * ∑ i, |w i - v i| ≤
        4 * (2 * gaussianMomentDimension d L / M) :=
      mul_le_mul_of_nonneg_left hl1wv (by norm_num)
    exact hround.trans (by linarith)
  · intro x hxX
    have hrelative :
        |finiteGaussianMixture w z x / gaussianMixture μ ϑ x - 1| ≤
          gaussianMomentRelativeError T S L := by
      simpa only [gaussianMomentRelativeError] using hrelative0 x hxX
    have hrelativeNonneg : 0 ≤ gaussianMomentRelativeError T S L := by
      unfold gaussianMomentRelativeError
      have hB : 0 ≤ T * S + S ^ 2 / 2 := by positivity
      positivity
    have hsmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
        ∑ i, |v i - w i| ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left hl1vw (Real.exp_pos _).le).trans hweightSmall
    have hlog := abs_log_rounded_finiteGaussianMixture_sub_gaussianMixture_le
      μ ϑ hϑmeas w v z η x hw.1 hvnonneg hw.2 hvsum
      hT hS hε.le (hXbound x hxX)
      (fun i ↦ hKbound (z i) (hzK i))
      (fun i ↦ hKbound (η i) (hηK i)) hθη hsmall
      hrelativeNonneg hrelativeHalf hrelative
    have hmass :
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) * ∑ i, |v i - w i| ≤
          2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
            (2 * gaussianMomentDimension d L / M) :=
      mul_le_mul_of_nonneg_left hl1vw (by positivity)
    exact hlog.trans (by linarith)
