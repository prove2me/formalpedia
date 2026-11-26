-- Prove2me | solution 1 for ReweightedNPMLE.gaussian_effective_dimension_full_support
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:18:21.374131+00:00
-- url     : https://prove2.me/submissions/541ccd31-9602-44ba-b5b5-8210c434ca2a

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
import Theorems.Thm_ReweightedNPMLE_effective_dimension_full_support
import Theorems.Thm_ReweightedNPMLE_gaussianFittedSet_lower_bound
import Theorems.Thm_ReweightedNPMLE_gaussian_convexHull_projection_error
import Theorems.Thm_ReweightedNPMLE_mem_gaussianFittedSet_iff_exists_finite_mixture

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

-- Inline helpers preserved from ReweightedNPMLE.PolynomialMoments.
section
namespace ReweightedNPMLE

open scoped BigOperators
open Finset Fintype



/-- There are exactly `choose (D + d) d` monomials of total degree at most `D`. -/
theorem card_monomialCoord (d D : ℕ) :
    Fintype.card (MonomialCoord d D) = (D + d).choose d := by
  rw [Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have h : d + 1 + D - 1 = D + d := by omega
  rw [h, Nat.choose_symm_add]

























































































































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianWidth.
section
/-!
# Finite-dimensional relative-width transfer

These lemmas formalize the linear-algebra end of Proposition 4.1: a uniform
coordinatewise Taylor approximation by vectors in a low-dimensional subspace
implies the stated Euclidean residual-width bound for its orthogonal
projection.
-/

open scoped BigOperators ComplexConjugate

namespace ReweightedNPMLE







/-! ## The concrete Gaussian Taylor subspace -/











/-- Its rank is at most `1 + choose (L+d) d`, exactly as in Proposition 4.1. -/
theorem finrank_gaussianTaylorSubspace_le {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) :
    Module.finrank ℝ (gaussianTaylorSubspace L x v₀) ≤
      1 + (L + d).choose d := by
  change Module.finrank ℝ
      (Submodule.span ℝ (Set.range (gaussianWidthGenerator L x v₀))) ≤ _
  calc
    _ ≤ Fintype.card (Option (MonomialCoord d L)) :=
      finrank_range_le_card (R := ℝ) (gaussianWidthGenerator L x v₀)
    _ = 1 + (L + d).choose d := by
      rw [Fintype.card_option, card_monomialCoord]
      omega

















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

theorem relative_gaussian_fitted_mem_convexHull {d n : ℕ}
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (K : Set (Point d))
    {v : Fin n → ℝ} (hv : v ∈ gaussianFittedSet x K) :
    WithLp.toLp 2 (relativeFittedVector v₀ v) ∈
      convexHull ℝ (relativeGaussianAtom x v₀ '' K) := by
  classical
  obtain ⟨ι, hι, p, θ, hp, hpsum, hθ, hval⟩ :=
    (mem_gaussianFittedSet_iff_exists_finite_mixture x K v).mp hv
  letI : Fintype ι := hι
  refine mem_convexHull_of_exists_fintype p (fun j ↦ relativeGaussianAtom x v₀ (θ j))
    hp hpsum (fun j ↦ ⟨θ j, hθ j, rfl⟩) ?_
  apply WithLp.ofLp_injective 2
  funext i
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, relativeGaussianAtom, relativeFittedVector]
  have hi := congrFun hval i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, gaussianScoreFeature] at hi
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hpsum, ← hi, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gaussian_relativeFittedSet_width {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (K : Set (Point d))
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hK : ∀ θ ∈ K, ‖θ‖ ≤ S)
    (hv₀ : v₀ ∈ gaussianFittedSet x K) :
    ∀ u ∈ relativeFittedSet (gaussianFittedSet x K) v₀,
      ‖WithLp.toLp 2 u - (gaussianTaylorSubspace L x v₀).starProjection (WithLp.toLp 2 u)‖ ≤
        Real.sqrt n * (Real.exp (2 * T * S + S ^ 2 / 2) *
          (T * S) ^ (L + 1) / (L + 1).factorial) := by
  rintro u ⟨v, hv, rfl⟩
  exact gaussian_convexHull_projection_error L x v₀ K hT hS hx hK
    (gaussianFittedSet_lower_bound x K hT hS hx hK hv₀)
    (relative_gaussian_fitted_mem_convexHull x v₀ K hv)















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
/-- Finite-sample conditional Gaussian structural bounds with the explicit
Taylor rank and remainder. No assumption about sampling or model correctness
is used. The later polylogarithmic specialization only has to choose `L` and
verify the two displayed scale conditions. -/
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} [Nonempty (Fin n)] (L : ℕ) {α q T S : ℝ}
    (hq : 1 ≤ q) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (x : Fin n → Point d) (hx : ∀ i, ‖x i‖ ≤ T)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθbound : ∀ a, ‖θ a‖ ≤ S)
    (hscale : 10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + effectiveQ n q) ≤ α)
    (hwidthScale : gaussianTaylorResidual n T S L *
      Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1) :
    let A := fun a : Θ ↦ gaussianScoreFeature x (θ a)
    let C := convexHull ℝ (range A)
    let vhat := fittedValueSelection C
      (positive_kernel_hull_properties A ((continuous_gaussianScoreFeature x).comp hθ)
        (fun _ _ ↦ Real.exp_pos _)).1
      (positive_kernel_hull_properties A ((continuous_gaussianScoreFeature x).comp hθ)
        (fun _ _ ↦ Real.exp_pos _)).2.1
      (positive_kernel_hull_properties A ((continuous_gaussianScoreFeature x).comp hθ)
        (fun _ _ ↦ Real.exp_pos _)).2.2
    let v₀ := vhat 1
    ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
      (gammaProductMeasure n α α).real Gᶜ ≤ 3 * Real.exp (-q) ∧
      ∀ w ∈ G, (∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)) ∧
        w ∈ positiveVectors n ∧
        (maximumExtremeSupport A vhat w : ℝ) ≤
          10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + q) ∧
        (∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ →
          (μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤
            10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + q)) ∧
        0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ∧
        weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ≤
          10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + q) / α ∧
        (∑ i, (fittedLogRatio v₀ (vhat w) i) ^ 2) ≤
          10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + q) / α ∧
        ∀ τ : ℝ, 0 ≤ τ → τ < 1 / 3072 → ∀ v ∈ C,
          weightedLogLikelihood w (vhat w) - τ ≤ weightedLogLikelihood w v →
          0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
          weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ≤
            10000000 * ((((1 + (L + d).choose d : ℕ) : ℝ) + q) / α + τ) ∧
          (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤
            10000000 * ((((1 + (L + d).choose d : ℕ) : ℝ) + q) / α + τ) := by
  dsimp only
  let A := fun a : Θ ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hApos : ∀ a i, 0 < A a i := fun a i ↦ Real.exp_pos _
  let C := convexHull ℝ (range A)
  let hb := positive_kernel_hull_properties A hA hApos
  let vhat := fittedValueSelection C hb.1 hb.2.1 hb.2.2
  have hCeq : C = gaussianFittedSet x (range θ) := by
    unfold C gaussianFittedSet
    congr 1
    ext a
    simp only [mem_range, mem_image, A]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨θ b, ⟨b, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
  have hwidth : ∀ u ∈ relativeFittedSet C (vhat 1),
      ‖WithLp.toLp 2 u - (gaussianTaylorSubspace L x (vhat 1)).starProjection
        (WithLp.toLp 2 u)‖ ≤ gaussianTaylorResidual n T S L := by
    have hv₀ : vhat 1 ∈ gaussianFittedSet x (range θ) :=
      hCeq ▸ (fittedValueSelection_isMax C hb.1 hb.2.1 hb.2.2 1).1
    intro u hu
    rw [hCeq] at hu
    exact gaussian_relativeFittedSet_width L x (vhat 1) (range θ) hT hS hx
      (fun b hb ↦ by rcases hb with ⟨a, rfl⟩; exact hθbound a) hv₀ u hu
  have hη : 0 ≤ gaussianTaylorResidual n T S L := by
    unfold gaussianTaylorResidual
    positivity
  obtain ⟨hstat, G, hGmeas, hGprob, hG⟩ := effective_dimension_full_support hq hη hscale
    hwidthScale A hA hApos (gaussianTaylorSubspace L x (vhat 1))
    (finrank_gaussianTaylorSubspace_le L x (vhat 1)) hwidth
  refine ⟨G, hGmeas, hGprob, ?_⟩
  intro w hw
  obtain ⟨hcoord, hwpos, hs, hattain, hall, hnonneg, hloss, hlog, hnear⟩ := hG w hw
  exact ⟨hcoord, hwpos, hs, hall, hnonneg, hloss, hlog, hnear⟩
