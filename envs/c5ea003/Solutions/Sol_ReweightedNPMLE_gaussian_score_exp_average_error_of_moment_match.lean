-- Prove2me | solution 1 for ReweightedNPMLE.gaussian_score_exp_average_error_of_moment_match
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:03:59.466147+00:00
-- url     : https://prove2.me/submissions/9dea0328-7b0c-4cbf-bc8a-3506081b450c

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Theorems.Thm_ReweightedNPMLE_IsMonomialCombination_integrable_comp_of_feature
import Theorems.Thm_ReweightedNPMLE_IsMonomialCombination_weighted_sum_eq_integral
import Theorems.Thm_ReweightedNPMLE_coordinateGaussianTruncatedScoreExp_isMonomialCombination
import Theorems.Thm_ReweightedNPMLE_real_exp_taylor_remainder_bound

open ReweightedNPMLE

open scoped BigOperators
open Finset Fintype
open ReweightedNPMLE in
/-- Exact matching through degree `2*L` turns the two Taylor remainders into
the paper's `2 exp(B) B^(L+1)/(L+1)!` mixture approximation bound. -/
theorem solution
    {Θ : Type*} [MeasurableSpace Θ] {d L : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Fin d → ℝ)
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → Fin d → ℝ)
    (hw : w ∈ stdSimplex ℝ ι)
    (hint : MeasureTheory.Integrable
      (fun a ↦ monomialFeature d (2 * L) (θ a)) μ)
    (hmom : ∑ i, w i • monomialFeature d (2 * L) (z i) =
      ∫ a, monomialFeature d (2 * L) (θ a) ∂μ)
    (x : Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hzB : ∀ i, |coordinateGaussianScore x (z i)| ≤ B)
    (hθB : ∀ᵐ a ∂μ, |coordinateGaussianScore x (θ a)| ≤ B)
    (hexp : MeasureTheory.Integrable
      (fun a ↦ Real.exp (coordinateGaussianScore x (θ a))) μ) :
    |(∑ i, w i * Real.exp (coordinateGaussianScore x (z i))) -
        ∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ| ≤
      2 * (Real.exp B * B ^ (L + 1) / (L + 1).factorial) := by
  classical
  let trunc : (Fin d → ℝ) → ℝ := coordinateGaussianTruncatedScoreExp L x
  let R : ℝ := Real.exp B * B ^ (L + 1) / (L + 1).factorial
  have htruncPoly : IsMonomialCombination (d := d) (D := 2 * L) trunc :=
    coordinateGaussianTruncatedScoreExp_isMonomialCombination L x
  have htruncInt : MeasureTheory.Integrable (fun a ↦ trunc (θ a)) μ :=
    htruncPoly.integrable_comp_of_feature μ θ hint
  have hpoly : ∑ i, w i * trunc (z i) = ∫ a, trunc (θ a) ∂μ :=
    htruncPoly.weighted_sum_eq_integral w z μ θ hint hmom
  have hfinite :
      |(∑ i, w i * Real.exp (coordinateGaussianScore x (z i))) -
          ∑ i, w i * trunc (z i)| ≤ R := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i, (w i * Real.exp (coordinateGaussianScore x (z i)) -
          w i * trunc (z i))| ≤
          ∑ i, |w i * Real.exp (coordinateGaussianScore x (z i)) -
            w i * trunc (z i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, w i *
          |Real.exp (coordinateGaussianScore x (z i)) - trunc (z i)| := by
            apply Fintype.sum_congr
            intro i
            rw [← mul_sub, abs_mul, abs_of_nonneg (hw.1 i)]
      _ ≤ ∑ i, w i * R := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left
              (real_exp_taylor_remainder_bound L hB (hzB i)) (hw.1 i)
      _ = R := by rw [← Finset.sum_mul, hw.2, one_mul]
  have hintegral :
      |(∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ) -
          ∫ a, trunc (θ a) ∂μ| ≤ R := by
    rw [← MeasureTheory.integral_sub hexp htruncInt]
    have hnorm := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := μ) (C := R) (f := fun a ↦
        Real.exp (coordinateGaussianScore x (θ a)) - trunc (θ a))
      (hθB.mono fun a ha ↦ real_exp_taylor_remainder_bound L hB ha)
    simpa only [Real.norm_eq_abs, MeasureTheory.probReal_univ, mul_one] using hnorm
  have hdecomp :
      (∑ i, w i * Real.exp (coordinateGaussianScore x (z i))) -
          ∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ =
        ((∑ i, w i * Real.exp (coordinateGaussianScore x (z i))) -
          ∑ i, w i * trunc (z i)) +
        ((∫ a, trunc (θ a) ∂μ) -
          ∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ) := by
    rw [hpoly]
    ring
  rw [hdecomp]
  calc
    |_ + _| ≤
        |(∑ i, w i * Real.exp (coordinateGaussianScore x (z i))) -
          ∑ i, w i * trunc (z i)| +
        |(∫ a, trunc (θ a) ∂μ) -
          ∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ| := abs_add_le _ _
    _ ≤ R + R := add_le_add hfinite (by simpa [abs_sub_comm] using hintegral)
    _ = 2 * R := by ring
