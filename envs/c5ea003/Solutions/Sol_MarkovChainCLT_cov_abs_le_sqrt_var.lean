-- Prove2me | solution 1 for MarkovChainCLT.cov_abs_le_sqrt_var
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:21:00.521295+00:00
-- url     : https://prove2.me/submissions/1195e0ac-7296-4f99-af02-d80359084e62

import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U V : Ω → ℝ)
    (hU : MemLp U 2 P) (hV : MemLp V 2 P) :
    |cov[U, V; P]| ≤ Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]) := by
  have hU_int : Integrable U P := hU.integrable (by norm_num)
  have hV_int : Integrable V P := hV.integrable (by norm_num)
  have hUc : MemLp (fun ω => U ω - P[U]) 2 P := hU.sub (memLp_const _)
  have hVc : MemLp (fun ω => V ω - P[V]) 2 P := hV.sub (memLp_const _)
  -- cov as integral of centered product
  have hcov : cov[U, V; P] = ∫ ω, (U ω - P[U]) * (V ω - P[V]) ∂P := rfl
  have hvarU : Var[U; P] = ∫ ω, (U ω - P[U]) ^ 2 ∂P := by
    rw [variance_eq_integral hU.aemeasurable]
  have hvarV : Var[V; P] = ∫ ω, (V ω - P[V]) ^ 2 ∂P := by
    rw [variance_eq_integral hV.aemeasurable]
  rw [hcov, hvarU, hvarV]
  -- |∫ f g| ≤ ∫ |f g| = ∫ |f| |g| ≤ sqrt(∫|f|^2) sqrt(∫|g|^2)
  calc |∫ ω, (U ω - P[U]) * (V ω - P[V]) ∂P|
      ≤ ∫ ω, |(U ω - P[U]) * (V ω - P[V])| ∂P := abs_integral_le_integral_abs
    _ = ∫ ω, |U ω - P[U]| * |V ω - P[V]| ∂P := by
        congr with ω
        rw [abs_mul]
    _ ≤ (∫ ω, |U ω - P[U]| ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2) *
        (∫ ω, |V ω - P[V]| ^ (2 : ℝ) ∂P) ^ ((1 : ℝ) / 2) := by
        apply integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
        · exact Eventually.of_forall fun ω => abs_nonneg _
        · exact Eventually.of_forall fun ω => abs_nonneg _
        · -- MemLp |U-EU| 2
          have : MemLp (fun ω => |U ω - P[U]|) 2 P := hUc.abs
          simpa using this
        · have : MemLp (fun ω => |V ω - P[V]|) 2 P := hVc.abs
          simpa using this
    _ = Real.sqrt (∫ ω, (U ω - P[U]) ^ 2 ∂P) * Real.sqrt (∫ ω, (V ω - P[V]) ^ 2 ∂P) := by
        have e1 : (∫ ω, |U ω - P[U]| ^ (2 : ℝ) ∂P) = ∫ ω, (U ω - P[U]) ^ 2 ∂P := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [Real.rpow_two, sq_abs]
        have e2 : (∫ ω, |V ω - P[V]| ^ (2 : ℝ) ∂P) = ∫ ω, (V ω - P[V]) ^ 2 ∂P := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [Real.rpow_two, sq_abs]
        rw [e1, e2]
        congr 1 <;> rw [Real.sqrt_eq_rpow] <;> norm_num
