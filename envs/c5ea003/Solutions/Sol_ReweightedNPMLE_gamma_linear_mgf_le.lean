-- Prove2me | solution 1 for ReweightedNPMLE.gamma_linear_mgf_le
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:10:35.086935+00:00
-- url     : https://prove2.me/submissions/1b4a2be6-dbcb-47e1-93a6-6525e6568c83

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_centered_gamma_mgf
import Theorems.Thm_ReweightedNPMLE_log_one_add_ge_sub_sq_half

-- Inline helpers preserved from ReweightedNPMLE.GammaProjection.
section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace ReweightedNPMLE



theorem centered_gamma_mgf_le_exp_sq {α t : ℝ} (hα : 0 < α)
    (ht : |t| ≤ α / 2) :
    ∫ x, Real.exp (t * (x - 1)) ∂gammaMeasure α α ≤
      Real.exp (t ^ 2 / α) := by
  have htlt : t < α := by
    have := le_abs_self t
    linarith
  rw [centered_gamma_mgf hα htlt]
  let y : ℝ := t / α
  have hyabs : |y| ≤ 1 / 2 := by
    dsimp [y]
    rw [abs_div, abs_of_pos hα]
    exact (div_le_iff₀ hα).2 (by nlinarith)
  have hypos : 0 < 1 - y := by
    have := le_abs_self y
    linarith
  have hlog : -y - Real.log (1 - y) ≤ y ^ 2 := by
    have h := log_one_add_ge_sub_sq_half (u := -y) (by
      have := le_of_abs_le hyabs
      linarith)
    have h' : -y - y ^ 2 ≤ Real.log (1 - y) := by
      simpa [sub_eq_add_neg] using h
    linarith
  rw [Real.rpow_def_of_pos hypos]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [y] at hlog ⊢
  have hscaled := mul_le_mul_of_nonneg_left hlog hα.le
  field_simp [hα.ne'] at hscaled ⊢
  nlinarith













/-! ### A Euclidean half-net with the paper's `5 ^ r` cardinality bound -/











end ReweightedNPMLE
end

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {n : ℕ} {α lam : ℝ} (hα : 0 < α)
    (hlam : |lam| ≤ Real.sqrt α / 2) (v : Fin n → ℝ)
    (hv : ∑ i, v i ^ 2 ≤ 1) :
    ∫ w, Real.exp (lam * Real.sqrt α * ∑ i, v i * (w i - 1))
        ∂gammaProductMeasure n α α ≤ Real.exp (lam ^ 2) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  let t : Fin n → ℝ := fun i ↦ lam * Real.sqrt α * v i
  have hαsqrt : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  have habsv (i : Fin n) : |v i| ≤ 1 := by
    have hi : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i)
    have : v i ^ 2 ≤ 1 := hi.trans hv
    nlinarith [abs_nonneg (v i), sq_abs (v i)]
  have ht (i : Fin n) : |t i| ≤ α / 2 := by
    rw [show |t i| = |lam| * Real.sqrt α * |v i| by
      simp [t, abs_mul, abs_of_nonneg (Real.sqrt_nonneg α)]]
    calc
      |lam| * Real.sqrt α * |v i| ≤
          (Real.sqrt α / 2) * Real.sqrt α * |v i| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hlam (Real.sqrt_nonneg α)) (abs_nonneg _)
      _ ≤ (Real.sqrt α / 2) * Real.sqrt α * 1 := by
        exact mul_le_mul_of_nonneg_left (habsv i) (by positivity)
      _ = Real.sqrt α ^ 2 / 2 := by ring
      _ = α / 2 := by rw [hαsqrt]
  have htlt (i : Fin n) : t i < α := by
    have hi := le_abs_self (t i)
    linarith [ht i]
  have hfun : (fun w : Fin n → ℝ ↦
      Real.exp (lam * Real.sqrt α * ∑ i, v i * (w i - 1))) =
      (fun w ↦ ∏ i, Real.exp (t i * (w i - 1))) := by
    funext w
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [t]
    ring
  rw [hfun]
  change (∫ w, ∏ i, Real.exp (t i * (w i - 1))
      ∂Measure.pi (fun _ : Fin n ↦ gammaMeasure α α)) ≤ _
  have hfactor :
      (∫ w, ∏ i, Real.exp (t i * (w i - 1))
        ∂Measure.pi (fun _ : Fin n ↦ gammaMeasure α α)) =
      ∏ i, ∫ x, Real.exp (t i * (x - 1)) ∂gammaMeasure α α :=
    integral_fintype_prod_eq_prod
      (fun i : Fin n ↦ fun x : ℝ ↦ Real.exp (t i * (x - 1)))
  rw [hfactor]
  calc
    ∏ i, ∫ x, Real.exp (t i * (x - 1)) ∂gammaMeasure α α ≤
        ∏ i, Real.exp ((t i) ^ 2 / α) := by
      apply Finset.prod_le_prod
      · intro i _
        rw [centered_gamma_mgf hα (htlt i)]
        have hbase : 0 < 1 - t i / α := by
          rw [sub_pos, div_lt_one hα]
          exact htlt i
        exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hbase.le _)
      · intro i _
        exact centered_gamma_mgf_le_exp_sq hα (ht i)
    _ = Real.exp (∑ i, (t i) ^ 2 / α) := by rw [Real.exp_sum]
    _ ≤ Real.exp (lam ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hsum : (∑ i, (t i) ^ 2 / α) = lam ^ 2 * ∑ i, v i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [t]
        rw [div_eq_iff hα.ne']
        rw [show (lam * Real.sqrt α * v i) ^ 2 =
          lam ^ 2 * Real.sqrt α ^ 2 * v i ^ 2 by ring, hαsqrt]
        ring
      rw [hsum]
      exact mul_le_of_le_one_right (sq_nonneg lam) hv
