-- Prove2me | solution 1 for ReweightedNPMLE.eventually_log_gaussianNetCardBound_paper_le
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:10:31.396114+00:00
-- url     : https://prove2.me/submissions/a68a9259-c6d1-40a4-ac73-07a96d32cfb6

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
import Theorems.Thm_ReweightedNPMLE_boundedLocationCellCount_cast_le
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianMomentDimension_add_two_le
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianMomentDimension_le_logScale_pow
import Theorems.Thm_ReweightedNPMLE_log_gaussianNetCardBound
import Theorems.Thm_ReweightedNPMLE_tendsto_id_div_log_atTop

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











/-- The logarithmic Taylor scale diverges. -/
theorem tendsto_gaussianPaperLogScale_atTop :
    Filter.Tendsto gaussianPaperLogScale Filter.atTop Filter.atTop := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  simpa only [gaussianPaperLogScale] using tendsto_id_div_log_atTop.comp hlog









































theorem gaussianPaperEpsilon_pos {n : ℕ} (hn : 0 < n) :
    0 < gaussianPaperEpsilon n := by
  unfold gaussianPaperEpsilon
  positivity



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





































/-- A convenient monotone form of the net entropy bound.  The parameters
`C` and `N` may subsequently be replaced by simple powers of the sample
size. -/
theorem log_gaussianNetCardBound_le (d L M : ℕ) {S ε C N : ℝ}
    (hC : 1 ≤ C)
    (hcell : (boundedLocationCellCount d S ε : ℝ) ≤ C)
    (hN : 1 ≤ N) (hgrid : (M : ℝ) + 1 ≤ N) :
    Real.log (gaussianNetCardBound d L M S ε : ℝ) ≤
      ((d * (gaussianMomentDimension d L + 1) : ℕ) : ℝ) * Real.log C +
        (gaussianMomentDimension d L : ℝ) * Real.log N := by
  rw [log_gaussianNetCardBound]
  have hcpos : 0 < (boundedLocationCellCount d S ε : ℝ) := by
    unfold boundedLocationCellCount
    positivity
  have hMpos : 0 < (M : ℝ) + 1 := by positivity
  have hlogcell : Real.log (boundedLocationCellCount d S ε : ℝ) ≤
      Real.log C := Real.log_le_log hcpos hcell
  have hloggrid : Real.log ((M : ℝ) + 1) ≤ Real.log N :=
    Real.log_le_log hMpos hgrid
  gcongr













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
/-- The explicit net constructed with the paper's choices has the claimed
entropy order `(log n)^(d+1)/(log log n)^d`.  This is stated as an eventual
finite-sample inequality with a displayed constant. -/
theorem solution
    (d : ℕ) {C S : ℝ} (hC : 0 < C) (hS : 0 ≤ S) :
    ∀ᶠ n in Filter.atTop,
      Real.log (gaussianNetCardBound d (gaussianPaperMomentOrder C n)
        (gaussianPaperWeightDenominator d C n) S
        (gaussianPaperEpsilon n) : ℝ) ≤
      17 * ((d : ℝ) + 1) * ((4 * C + 1) ^ d + 1) *
        gaussianPaperLogScale n ^ d * Real.log (n : ℝ) := by
  let A : ℝ := 2 * S * ((d : ℝ) + 2) + 1
  have hAevent : ∀ᶠ n : ℕ in Filter.atTop, A ≤ n := by
    exact tendsto_natCast_atTop_atTop.eventually_ge_atTop A
  filter_upwards [hAevent,
    eventually_gaussianMomentDimension_add_two_le d hC,
    eventually_gaussianMomentDimension_le_logScale_pow d hC,
    tendsto_gaussianPaperLogScale_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (2 : ℕ)] with n hAn hkTwo hkScale hscale hnTwo
  let L := gaussianPaperMomentOrder C n
  let M := gaussianPaperWeightDenominator d C n
  let k := gaussianMomentDimension d L
  have hn : 0 < n := lt_of_lt_of_le (by omega) hnTwo
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnPowOne : (1 : ℝ) ≤ (n : ℝ) ^ 16 := one_le_pow₀ hnOne
  have heps : 0 < gaussianPaperEpsilon n := gaussianPaperEpsilon_pos hn
  have hcell0 := boundedLocationCellCount_cast_le d hS heps
  have hcellFormula :
      2 * S * ((d : ℝ) + 2) / gaussianPaperEpsilon n + 1 =
        2 * S * ((d : ℝ) + 2) * (n : ℝ) ^ 16 + 1 := by
    unfold gaussianPaperEpsilon
    field_simp
  have hcell : (boundedLocationCellCount d S (gaussianPaperEpsilon n) : ℝ) ≤
      (n : ℝ) ^ 17 := by
    calc
      (boundedLocationCellCount d S (gaussianPaperEpsilon n) : ℝ) ≤
          2 * S * ((d : ℝ) + 2) / gaussianPaperEpsilon n + 1 := hcell0
      _ = 2 * S * ((d : ℝ) + 2) * (n : ℝ) ^ 16 + 1 := hcellFormula
      _ ≤ A * (n : ℝ) ^ 16 := by
        dsimp [A]
        nlinarith [sq_nonneg ((n : ℝ) ^ 8)]
      _ ≤ (n : ℝ) * (n : ℝ) ^ 16 :=
        mul_le_mul_of_nonneg_right hAn (pow_nonneg hnreal.le _)
      _ = (n : ℝ) ^ 17 := by ring
  have hMupper := (gaussianPaperWeightDenominator_bounds d C hn).2
  have hkTwo' : (k : ℝ) + 2 ≤ n := by simpa only [k, L] using hkTwo
  have hgrid : (M : ℝ) + 1 ≤ (n : ℝ) ^ 17 := by
    calc
      (M : ℝ) + 1 ≤ (k : ℝ) * (n : ℝ) ^ 16 + 2 := by
        dsimp [M, k, L] at hMupper ⊢
        linarith
      _ ≤ ((k : ℝ) + 2) * (n : ℝ) ^ 16 := by
        nlinarith
      _ ≤ (n : ℝ) * (n : ℝ) ^ 16 :=
        mul_le_mul_of_nonneg_right hkTwo' (pow_nonneg hnreal.le _)
      _ = (n : ℝ) ^ 17 := by ring
  have hpowerOne : (1 : ℝ) ≤ (n : ℝ) ^ 17 := one_le_pow₀ hnOne
  have hraw := log_gaussianNetCardBound_le d L M
    hpowerOne hcell hpowerOne hgrid
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnOne
  rw [Real.log_pow] at hraw
  push_cast at hraw
  have hraw' :
      Real.log (gaussianNetCardBound d L M S (gaussianPaperEpsilon n) : ℝ) ≤
        17 * ((d : ℝ) + 1) * ((k : ℝ) + 1) * Real.log (n : ℝ) := by
    calc
      Real.log (gaussianNetCardBound d L M S (gaussianPaperEpsilon n) : ℝ) ≤
          (d * (k + 1)) * (17 * Real.log (n : ℝ)) +
            k * (17 * Real.log (n : ℝ)) := hraw
      _ ≤ 17 * ((d : ℝ) + 1) * ((k : ℝ) + 1) * Real.log (n : ℝ) := by
        nlinarith
  have hkScale' : (k : ℝ) ≤
      (4 * C + 1) ^ d * gaussianPaperLogScale n ^ d := by
    simpa only [k, L, mul_pow] using hkScale
  have hscalePow : (1 : ℝ) ≤ gaussianPaperLogScale n ^ d :=
    one_le_pow₀ hscale
  have hkOne : (k : ℝ) + 1 ≤
      ((4 * C + 1) ^ d + 1) * gaussianPaperLogScale n ^ d := by
    nlinarith [show 0 ≤ (4 * C + 1) ^ d by positivity]
  calc
    Real.log (gaussianNetCardBound d (gaussianPaperMomentOrder C n)
        (gaussianPaperWeightDenominator d C n) S
        (gaussianPaperEpsilon n) : ℝ) =
        Real.log (gaussianNetCardBound d L M S (gaussianPaperEpsilon n) : ℝ) := rfl
    _ ≤ 17 * ((d : ℝ) + 1) * ((k : ℝ) + 1) * Real.log (n : ℝ) := hraw'
    _ ≤ 17 * ((d : ℝ) + 1) * ((4 * C + 1) ^ d + 1) *
        gaussianPaperLogScale n ^ d * Real.log (n : ℝ) := by
      calc
        17 * ((d : ℝ) + 1) * ((k : ℝ) + 1) * Real.log (n : ℝ) =
            (17 * ((d : ℝ) + 1) * Real.log (n : ℝ)) * ((k : ℝ) + 1) := by ring
        _ ≤ (17 * ((d : ℝ) + 1) * Real.log (n : ℝ)) *
            (((4 * C + 1) ^ d + 1) * gaussianPaperLogScale n ^ d) :=
          mul_le_mul_of_nonneg_left hkOne (by positivity)
        _ = 17 * ((d : ℝ) + 1) * ((4 * C + 1) ^ d + 1) *
            gaussianPaperLogScale n ^ d * Real.log (n : ℝ) := by ring
