-- Prove2me | solution 1 for ReweightedNPMLE.effective_dimension_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:15:33.272428+00:00
-- url     : https://prove2.me/submissions/46ae077c-1b1d-4bad-afe5-024799164b4c

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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
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
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedLocalization
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_GammaEffectiveEvent
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_effective_dimension_finite_support_common_event

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

-- Inline helpers preserved from ReweightedNPMLE.EffectiveSparsification.
section
/-!
# Effective-dimension sparsification on a common event

Gamma concentration instantiates radial localization and the determinant
support tail. All near-optimal fitted vectors obey the error bounds on the
same measurable event. The support statistic here is the maximum independent
finite representation; identification with full measure-fiber extreme points
is a separate theorem, not an assumption hidden in this result.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE





theorem effective_dimension_scale_bounds {n r : ℕ} [Nonempty (Fin n)]
    {α q : ℝ} (hq : 1 ≤ q)
    (hscale : 10000000 * ((r : ℝ) + effectiveQ n q) ≤ α) :
    0 < α ∧ 1 ≤ effectiveQ n q ∧ 1 ≤ effectiveN r q ∧
      1024 * effectiveQ n q ≤ α ∧ 2359296 * effectiveN r q ≤ α ∧
      12288 ≤ α ∧ effectiveN r q ≤ 4 * ((r : ℝ) + q) := by
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hn1 : 1 ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n from Fin.pos_iff_nonempty.mpr inferInstance)
  have hlogn : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hlog5₀ : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog5₁ : Real.log (5 : ℝ) ≤ 4 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    norm_num at hh
    exact hh
  have hQ : q ≤ effectiveQ n q := by dsimp [effectiveQ]; linarith
  have hN₀ : q ≤ effectiveN r q := by
    dsimp [effectiveN]
    nlinarith [mul_nonneg hr hlog5₀]
  have hN₁ : effectiveN r q ≤ 4 * ((r : ℝ) + q) := by
    dsimp [effectiveN]
    nlinarith [mul_le_mul_of_nonneg_left hlog5₁ hr]
  have hNQ : effectiveN r q ≤ 4 * ((r : ℝ) + effectiveQ n q) := by linarith
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, hN₁⟩

theorem effective_dimension_support_numeric_bound {r k : ℕ} {q : ℝ}
    (hq : 1 ≤ q) (hk : 0 < k)
    (htail : Real.log (17 / 9 : ℝ) * ((k - 1 : ℕ) : ℝ) <
      1744 * effectiveN r q + 74 + q) :
    (k : ℝ) ≤ 10000000 * ((r : ℝ) + q) := by
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hlog5 : Real.log (5 : ℝ) ≤ 4 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    norm_num at hh
    exact hh
  have hN : effectiveN r q ≤ 4 * ((r : ℝ) + q) := by
    dsimp [effectiveN]
    nlinarith [mul_le_mul_of_nonneg_left hlog5 hr]
  have hκ : (1 / 4 : ℝ) ≤ Real.log (17 / 9 : ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 17 / 9 by norm_num)
    norm_num at hh
    linarith
  have hk1 : 1 ≤ k := hk
  rw [Nat.cast_sub hk1] at htail
  norm_num only [Nat.cast_one] at htail
  have hkr : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
  have hh := mul_le_mul_of_nonneg_right hκ (show 0 ≤ (k : ℝ) - 1 by linarith)
  nlinarith

theorem effective_dimension_error_numeric_bound {r : ℕ} {α q τ X Y : ℝ}
    (hα : 0 < α) (hq : 1 ≤ q) (hτ : 0 ≤ τ)
    (hX : α * X ≤ 592 * effectiveN r q + 26 + 13 * α * τ)
    (hY : α * Y ≤ 1152 * effectiveN r q + 48 + 24 * α * τ) :
    X ≤ 10000000 * (((r : ℝ) + q) / α + τ) ∧
    Y ≤ 10000000 * (((r : ℝ) + q) / α + τ) := by
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hlog5 : Real.log (5 : ℝ) ≤ 4 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    norm_num at hh
    exact hh
  have hN : effectiveN r q ≤ 4 * ((r : ℝ) + q) := by
    dsimp [effectiveN]
    nlinarith [mul_le_mul_of_nonneg_left hlog5 hr]
  have hατ : 0 ≤ α * τ := mul_nonneg hα.le hτ
  have heq : α * (10000000 * (((r : ℝ) + q) / α + τ)) =
      10000000 * ((r : ℝ) + q) + 10000000 * (α * τ) := by
    field_simp
  constructor
  · apply (mul_le_mul_iff_right₀ hα).mp
    rw [heq]
    nlinarith
  · apply (mul_le_mul_iff_right₀ hα).mp
    rw [heq]
    nlinarith



end ReweightedNPMLE
end

/-!
# Effective-dimension sparsification on a common event

Gamma concentration instantiates radial localization and the determinant
support tail. All near-optimal fitted vectors obey the error bounds on the
same measurable event. The support statistic here is the maximum independent
finite representation; identification with full measure-fiber extreme points
is a separate theorem, not an assumption hidden in this result.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Explicit universal constants for the finite-representation version of
effective sparsification. Every approximate-fit conclusion is simultaneous
over `v` and `tau` on the same measurable event. -/
theorem solution
    {n r : ℕ} [Nonempty (Fin n)] {α q η : ℝ}
    (hq : 1 ≤ q) (hη : 0 ≤ η)
    (hscale : 10000000 * ((r : ℝ) + effectiveQ n q) ≤ α)
    (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D) (hD : D ⊆ C)
    (hChull : C ⊆ convexHull ℝ D)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hrank : Module.finrank ℝ V ≤ r)
    (hwidth : ∀ u ∈ relativeFittedSet C (fittedValueSelection C hCcompact hCnonempty hCpos 1),
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η) :
    let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
    let v₀ := vhat 1
    ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
      (gammaProductMeasure n α α).real Gᶜ ≤ 3 * Real.exp (-q) ∧
      ∀ w ∈ G, (∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)) ∧
        w ∈ positiveVectors n ∧
        (maximumIndependentSupport D vhat w : ℝ) ≤ 10000000 * ((r : ℝ) + q) ∧
        0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ∧
        weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ≤
          10000000 * ((r : ℝ) + q) / α ∧
        (∑ i, (fittedLogRatio v₀ (vhat w) i) ^ 2) ≤ 10000000 * ((r : ℝ) + q) / α ∧
        ∀ (τ : ℝ), 0 ≤ τ → τ < 1 / 3072 → ∀ v ∈ C,
          weightedLogLikelihood w (vhat w) - τ ≤ weightedLogLikelihood w v →
          0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
          weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ≤
            10000000 * (((r : ℝ) + q) / α + τ) ∧
          (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤
            10000000 * (((r : ℝ) + q) / α + τ) := by
  have hb := effective_dimension_scale_bounds hq hscale
  obtain ⟨G, hGmeas, hGprob, hG⟩ := effective_dimension_finite_support_common_event hb.1 hq hη
    hwidthScale hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2.1
    C hC hCcompact hCnonempty hCpos D hDclosed hD hChull V hrank hwidth
  refine ⟨G, hGmeas, hGprob, ?_⟩
  intro w hw
  have hh := (hG w hw).2
  have hsupport := effective_dimension_support_numeric_bound hq hh.2.1 hh.2.2.1
  have hexact := hh.2.2.2 0 (by norm_num) (by norm_num)
    (fittedValueSelection C hCcompact hCnonempty hCpos w)
    (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1 (by simp)
  have herrors := effective_dimension_error_numeric_bound hb.1 hq (show (0 : ℝ) ≤ 0 by norm_num)
    hexact.2.2.1 hexact.2.2.2
  simp only [add_zero, ← mul_div_assoc] at herrors
  refine ⟨(hG w hw).1.1, hh.1, hsupport, hexact.2.1, herrors.1, herrors.2, ?_⟩
  intro τ hτ₀ hτ v hv hnear
  have hloc := hh.2.2.2 τ hτ₀ hτ v hv hnear
  have herr := effective_dimension_error_numeric_bound hb.1 hq hτ₀ hloc.2.2.1 hloc.2.2.2
  exact ⟨hloc.2.1, herr.1, herr.2⟩
