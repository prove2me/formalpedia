-- Prove2me | solution 1 for rademacher_matrix_operator_norm_2p_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-24T15:55:12.27573+00:00
-- url     : https://prove2.me/submissions/ccea95fe-af46-46a0-825f-3e47068669f5

import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_general_rademacher_matrix_2p_trace_moment
import Theorems.Thm_spectral_norm_pow_two_mul_le_trace_pow
import Theorems.Thm_double_factorial_central_quotient_le_two_p_pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Matrix MatrixCompletion
open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (hd : 0 < d)
    (H : ι → Matrix (Fin d) (Fin d) ℝ)
    (hHerm : ∀ c, (H c).IsHermitian)
    (normV : ℝ) (hnormVnn : 0 ≤ normV)
    (hVHerm : (∑ c : ι, H c * H c).IsHermitian)
    (hnormV : ∀ i, hVHerm.eigenvalues i ≤ normV)
    (p : ℕ) (hp : 1 ≤ p) :
    (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι)
        * spectralNorm (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c) ^ (2 * p))
      ^ ((1 : ℝ) / (2 * p))
      ≤ Real.sqrt (2 * p) * Real.sqrt normV * (d : ℝ) ^ ((1 : ℝ) / (2 * p)) := by
  classical
  set e : ℝ := (1 : ℝ) / (2 * p) with he
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp
  have h2ppos : (0 : ℝ) < 2 * p := by positivity
  have henn : 0 ≤ e := by rw [he]; positivity
  set Xeps : Finset ι → Matrix (Fin d) (Fin d) ℝ :=
    fun eps => (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c) with hX
  have hXHerm : ∀ eps, (Xeps eps).IsHermitian := by
    intro eps
    show (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c).IsHermitian
    refine Finset.sum_induction _ (fun M => Matrix.IsHermitian M)
      (fun A B hA hB => hA.add hB) Matrix.isHermitian_zero ?_
    intro c _
    exact (hHerm c).smul (IsSelfAdjoint.all _)
  set LHSinner : ℝ := ∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι)
      * spectralNorm (Xeps eps) ^ (2 * p) with hLHS
  set RHSeng : ℝ := ((Nat.factorial (2 * p) : ℝ) / ((2 ^ p : ℝ) * (Nat.factorial p : ℝ)))
      * normV ^ p * (d : ℝ) with hReng
  have step2 : LHSinner ≤ RHSeng := by
    have htm : LHSinner ≤ ∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι)
        * Matrix.trace ((Xeps eps) ^ (2 * p)) := by
      apply Finset.sum_le_sum
      intro eps _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact spectral_norm_pow_two_mul_le_trace_pow hd (Xeps eps) (hXHerm eps) p
    refine htm.trans ?_
    have heng := general_rademacher_matrix_2p_trace_moment H hHerm normV hnormVnn hVHerm hnormV p
    convert heng using 2
  have hLHSnn : 0 ≤ LHSinner := by
    rw [hLHS]
    apply Finset.sum_nonneg
    intro eps _
    apply mul_nonneg (by positivity)
    rw [pow_mul]
    positivity
  have step3 : LHSinner ^ e ≤ RHSeng ^ e := Real.rpow_le_rpow hLHSnn step2 henn
  have hRle : RHSeng ≤ (2 * p : ℝ) ^ p * normV ^ p * (d : ℝ) := by
    rw [hReng]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right (double_factorial_central_quotient_le_two_p_pow p) (by positivity)
  have hRengnn : 0 ≤ RHSeng := by rw [hReng]; positivity
  have step4a : RHSeng ^ e ≤ ((2 * p : ℝ) ^ p * normV ^ p * (d : ℝ)) ^ e :=
    Real.rpow_le_rpow hRengnn hRle henn
  have key : ((2 * p : ℝ) ^ p * normV ^ p * (d : ℝ)) ^ e
      = Real.sqrt (2 * p) * Real.sqrt normV * (d : ℝ) ^ e := by
    have h2pnn : (0 : ℝ) ≤ 2 * p := le_of_lt h2ppos
    have hAnn : (0 : ℝ) ≤ (2 * p : ℝ) ^ p := by positivity
    have hBnn : (0 : ℝ) ≤ normV ^ p := by positivity
    have hABnn : (0 : ℝ) ≤ (2 * p : ℝ) ^ p * normV ^ p := mul_nonneg hAnn hBnn
    rw [Real.mul_rpow hABnn (by positivity), Real.mul_rpow hAnn hBnn]
    have hpe : (p : ℝ) * e = 1 / 2 := by rw [he]; field_simp
    have hApow : ((2 * p : ℝ) ^ p) ^ e = Real.sqrt (2 * p) := by
      rw [← Real.rpow_natCast (2 * p : ℝ) p, ← Real.rpow_mul h2pnn, hpe, Real.sqrt_eq_rpow]
    have hBpow : (normV ^ p) ^ e = Real.sqrt normV := by
      rw [← Real.rpow_natCast normV p, ← Real.rpow_mul hnormVnn, hpe, Real.sqrt_eq_rpow]
    rw [hApow, hBpow]
  calc LHSinner ^ e ≤ RHSeng ^ e := step3
    _ ≤ ((2 * p : ℝ) ^ p * normV ^ p * (d : ℝ)) ^ e := step4a
    _ = Real.sqrt (2 * p) * Real.sqrt normV * (d : ℝ) ^ e := key

#print axioms solution
