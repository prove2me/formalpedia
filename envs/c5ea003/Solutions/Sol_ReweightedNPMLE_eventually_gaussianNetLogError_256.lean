-- Prove2me | solution 1 for ReweightedNPMLE.eventually_gaussianNetLogError_256
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:09:03.200325+00:00
-- url     : https://prove2.me/submissions/8223c32f-bbd6-4020-8dea-702ad4381da7

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
import Definitions.Def_ReweightedNPMLE_GaussianNearMLERate
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_eventually_exp_two_gaussianPaperTaylorArgument_le
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianMomentRelativeError_paper_le
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperSampleRadius_add_le_sq

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











/-- The ambient dimension of the moment feature is the number of monomials. -/
theorem finrank_monomialFeature (d D : ℕ) :
    Module.finrank ℝ (MonomialCoord d D → ℝ) = (D + d).choose d := by
  rw [Module.finrank_fintype_fun_eq_card, card_monomialCoord]













































































































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianNearMLERate.
section
/-!
# Explicit entropy arithmetic for the Gaussian near-MLE theorem

This module turns the finite Gaussian-mixture net cardinality appearing in
`GaussianNearMLE` into the binomial and logarithmic bounds used in the
paper's rate calculation.  It is kept separate from the probabilistic
argument so that the remaining asymptotic tuning can use a small, explicit
arithmetic interface.
-/

open scoped ENNReal
open Filter Topology MeasureTheory Set

namespace ReweightedNPMLE













































/-- The Gaussian moment dimension is always nonzero. -/
theorem gaussianMomentDimension_pos (d L : ℕ) :
    0 < gaussianMomentDimension d L := by
  change 0 < Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ)
  rw [finrank_monomialFeature]
  exact Nat.choose_pos (by omega)









theorem gaussianPaperWeightDenominator_pos
    (d : ℕ) (C : ℝ) {n : ℕ} (hn : 0 < n) :
    0 < gaussianPaperWeightDenominator d C n := by
  unfold gaussianPaperWeightDenominator
  apply Nat.ceil_pos.mpr
  exact mul_pos (by
      exact_mod_cast (gaussianMomentDimension_pos d
        (gaussianPaperMomentOrder C n)))
    (pow_pos (by exact_mod_cast hn) 16)

/-- Ceiling bounds for the paper's weight grid. -/
theorem gaussianPaperWeightDenominator_bounds
    (d : ℕ) (C : ℝ) {n : ℕ} (hn : 0 < n) :
    (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) *
          (n : ℝ) ^ 16 ≤ gaussianPaperWeightDenominator d C n ∧
      (gaussianPaperWeightDenominator d C n : ℝ) <
        (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) *
            (n : ℝ) ^ 16 + 1 := by
  have hbase : 0 ≤
      (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) *
        (n : ℝ) ^ 16 := by positivity
  unfold gaussianPaperWeightDenominator
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one hbase⟩

/-- Simplex rounding contributes at most `2 n⁻¹⁶`; the moment dimension
cancels from the choice `M = ceil(k n^16)`. -/
theorem gaussianPaper_weight_rounding_le
    (d : ℕ) (C : ℝ) {n : ℕ} (hn : 0 < n) :
    2 * gaussianMomentDimension d (gaussianPaperMomentOrder C n) /
        gaussianPaperWeightDenominator d C n ≤
      2 / (n : ℝ) ^ 16 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hMreal : (0 : ℝ) < gaussianPaperWeightDenominator d C n := by
    exact_mod_cast gaussianPaperWeightDenominator_pos d C hn
  have hceil := (gaussianPaperWeightDenominator_bounds d C hn).1
  rw [div_le_div_iff₀ hMreal (pow_pos hnreal 16)]
  nlinarith

theorem eventually_gaussianPaper_weightTerm_le
    (d : ℕ) {C S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (2 * gaussianPaperTaylorArgument d S b n) *
          (2 * gaussianMomentDimension d (gaussianPaperMomentOrder C n) /
            gaussianPaperWeightDenominator d C n) ≤
        2 / (n : ℝ) ^ 15 := by
  filter_upwards [eventually_exp_two_gaussianPaperTaylorArgument_le d hS hb,
    Filter.eventually_ge_atTop (1 : ℕ)] with n hexp hn
  have hnpos : 0 < n := by omega
  have hround := gaussianPaper_weight_rounding_le d C hnpos
  calc
    Real.exp (2 * gaussianPaperTaylorArgument d S b n) *
        (2 * gaussianMomentDimension d (gaussianPaperMomentOrder C n) /
          gaussianPaperWeightDenominator d C n) ≤
        (n : ℝ) * (2 / (n : ℝ) ^ 16) := by gcongr
    _ = 2 / (n : ℝ) ^ 15 := by field_simp

















/-- Numerical specialization used in the final theorem. -/
theorem eventually_gaussianMomentRelativeError_256_le
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianMomentRelativeError (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder 256 n) ≤ 2 / (n : ℝ) ^ 31 := by
  filter_upwards [eventually_gaussianMomentRelativeError_paper_le d
    (show (0 : ℝ) < 256 by norm_num) hS hb] with n hn
  convert hn using 1
  norm_num [Real.rpow_neg_natCast, zpow_neg, div_eq_mul_inv]
  rfl





























end ReweightedNPMLE
end

/-!
# Explicit entropy arithmetic for the Gaussian near-MLE theorem

This module turns the finite Gaussian-mixture net cardinality appearing in
`GaussianNearMLE` into the binomial and logarithmic bounds used in the
paper's rate calculation.  It is kept separate from the probabilistic
argument so that the remaining asymptotic tuning can use a small, explicit
arithmetic interface.
-/

open scoped ENNReal
open Filter Topology MeasureTheory Set

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The fully explicit paper net has total log-density error at most `1/n`,
which is the small-error hypothesis needed by the finite likelihood test. -/
theorem solution
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * gaussianNetLogError d (gaussianPaperMomentOrder 256 n)
        (gaussianPaperWeightDenominator d 256 n)
        (gaussianPaperSampleRadius d S b n) S (gaussianPaperEpsilon n) ≤ 1 := by
  filter_upwards [eventually_gaussianPaperSampleRadius_add_le_sq d hS hb,
    eventually_gaussianPaper_weightTerm_le d (C := (256 : ℝ)) hS hb,
    eventually_gaussianMomentRelativeError_256_le d hS hb,
    Filter.eventually_ge_atTop (2 : ℕ)] with n hT hweight hrel hn
  let T := gaussianPaperSampleRadius d S b n
  let L := gaussianPaperMomentOrder 256 n
  let M := gaussianPaperWeightDenominator d 256 n
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmesh : (T + S) * gaussianPaperEpsilon n ≤ 1 / (n : ℝ) ^ 14 := by
    unfold gaussianPaperEpsilon
    calc
      (T + S) * ((n : ℝ) ^ 16)⁻¹ ≤
          (n : ℝ) ^ 2 * ((n : ℝ) ^ 16)⁻¹ := by
        gcongr
      _ = 1 / (n : ℝ) ^ 14 := by field_simp
  have hδ : gaussianNetLogError d L M T S (gaussianPaperEpsilon n) ≤
      1 / (n : ℝ) ^ 14 + 4 / (n : ℝ) ^ 15 +
        4 / (n : ℝ) ^ 31 := by
    unfold gaussianNetLogError
    have hweight' : Real.exp (2 * (T * S + S ^ 2 / 2)) *
        (2 * gaussianMomentDimension d L / M) ≤ 2 / (n : ℝ) ^ 15 := by
      simpa only [T, L, M, gaussianPaperTaylorArgument] using hweight
    have hrel' : gaussianMomentRelativeError T S L ≤ 2 / (n : ℝ) ^ 31 := by
      simpa only [T, L] using hrel
    have hweightTwo :
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
            (2 * gaussianMomentDimension d L / M) ≤
          2 * (2 / (n : ℝ) ^ 15) := by
      calc
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
            (2 * gaussianMomentDimension d L / M) =
          2 * (Real.exp (2 * (T * S + S ^ 2 / 2)) *
            (2 * gaussianMomentDimension d L / M)) := by ring
        _ ≤ 2 * (2 / (n : ℝ) ^ 15) :=
          mul_le_mul_of_nonneg_left hweight' (by norm_num)
    have hrelTwo : 2 * gaussianMomentRelativeError T S L ≤
        2 * (2 / (n : ℝ) ^ 31) :=
      mul_le_mul_of_nonneg_left hrel' (by norm_num)
    calc
      (T + S) * gaussianPaperEpsilon n +
          2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
            (2 * gaussianMomentDimension d L / M) +
          2 * gaussianMomentRelativeError T S L ≤
        1 / (n : ℝ) ^ 14 + 2 * (2 / (n : ℝ) ^ 15) +
          2 * (2 / (n : ℝ) ^ 31) :=
        add_le_add (add_le_add hmesh hweightTwo) hrelTwo
      _ = 1 / (n : ℝ) ^ 14 + 4 / (n : ℝ) ^ 15 +
          4 / (n : ℝ) ^ 31 := by ring
  have h13pow : (2 : ℝ) ≤ (n : ℝ) ^ 13 := by
    calc
      (2 : ℝ) ≤ 2 ^ 13 := by norm_num
      _ ≤ (n : ℝ) ^ 13 := pow_le_pow_left₀ (by norm_num) hnTwo 13
  have h14pow : (16 : ℝ) ≤ (n : ℝ) ^ 14 := by
    calc
      (16 : ℝ) ≤ 2 ^ 14 := by norm_num
      _ ≤ (n : ℝ) ^ 14 := pow_le_pow_left₀ (by norm_num) hnTwo 14
  have h30pow : (16 : ℝ) ≤ (n : ℝ) ^ 30 := by
    calc
      (16 : ℝ) ≤ 2 ^ 30 := by norm_num
      _ ≤ (n : ℝ) ^ 30 := pow_le_pow_left₀ (by norm_num) hnTwo 30
  have h13 : 1 / (n : ℝ) ^ 13 ≤ 1 / 2 := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h13pow
  have h14 : 4 / (n : ℝ) ^ 14 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (pow_pos hnreal 14) (by norm_num)]
    nlinarith
  have h30 : 4 / (n : ℝ) ^ 30 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (pow_pos hnreal 30) (by norm_num)]
    nlinarith
  calc
    (n : ℝ) * gaussianNetLogError d L M T S (gaussianPaperEpsilon n) ≤
        (n : ℝ) * (1 / (n : ℝ) ^ 14 + 4 / (n : ℝ) ^ 15 +
          4 / (n : ℝ) ^ 31) := mul_le_mul_of_nonneg_left hδ hnreal.le
    _ = 1 / (n : ℝ) ^ 13 + 4 / (n : ℝ) ^ 14 +
        4 / (n : ℝ) ^ 30 := by field_simp
    _ ≤ 1 := by linarith
