-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.kernelMass_sub_approx2
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:47:44.165759+00:00
-- url     : https://prove2.me/submissions/a4b3113f-4352-4302-9a0a-ead58dd1af02

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateAssembly
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdosWeight_nonneg_of_lt
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdosWeight_sub_model_le
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_massLam_pos
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_model_tail_le
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_sigmaMoment_le_power_sharp
import Mathlib

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Close end AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

open scoped BigOperators

lemma sigmaR_eq_sum_divisors (m : ℕ) :
    sigmaR m = ∑ d ∈ m.divisors, (d : ℝ) := by
  rw [sigmaR, ArithmeticFunction.sigma_one_apply]
  norm_num

end AnalyticCombinatorics.Ch8.Partitions.Sigma
end

section
namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

open scoped BigOperators
open Finset

noncomputable section

private lemma Ioc_zero_eq_Icc_one (n : ℕ) :
    Finset.Ioc 0 n = Finset.Icc 1 n := by
  ext k
  simp [Nat.succ_le_iff]

private lemma sum_Icc_one_nat_cast (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (k : ℝ)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := n) (f := fun k : ℕ => (k : ℝ))
        (by omega)]
      rw [ih]
      norm_num
      ring

private lemma sigma_summatory_eq_triangular (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, sigmaR m) =
      ∑ q ∈ Finset.Icc 1 N,
        ((N / q : ℕ) : ℝ) * (((N / q : ℕ) : ℝ) + 1) / 2 := by
  classical
  have hnat :
      (∑ m ∈ Finset.Icc 1 N, ArithmeticFunction.sigma 1 m) =
        ∑ q ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / q), d := by
    have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
      (ArithmeticFunction.zeta : ArithmeticFunction ℕ)
      (ArithmeticFunction.pow 1) N
    rw [ArithmeticFunction.zeta_mul_pow_eq_sigma] at h
    have h' :
        (∑ m ∈ Finset.Icc 1 N, ArithmeticFunction.sigma 1 m) =
          ∑ q ∈ Finset.Icc 1 N,
            if q = 0 then 0 else ∑ d ∈ Finset.Icc 1 (N / q), d := by
      simpa [Ioc_zero_eq_Icc_one, ArithmeticFunction.zeta_apply,
        ArithmeticFunction.pow_apply] using h
    refine h'.trans ?_
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hq0 : q ≠ 0 := by
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      omega
    simp [hq0]
  have hreal := congrArg (fun a : ℕ => (a : ℝ)) hnat
  calc
    (∑ m ∈ Finset.Icc 1 N, sigmaR m)
        = ∑ q ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / q), (d : ℝ) := by
          simpa [sigmaR, Nat.cast_sum] using hreal
    _ = ∑ q ∈ Finset.Icc 1 N,
        ((N / q : ℕ) : ℝ) * (((N / q : ℕ) : ℝ) + 1) / 2 := by
          refine Finset.sum_congr rfl ?_
          intro q _hq
          exact sum_Icc_one_nat_cast (N / q)

private lemma hasSum_one_div_nat_sq :
    HasSum (fun n : ℕ => (((n : ℝ) ^ 2)⁻¹)) (Real.pi ^ 2 / 6) := by
  simpa [one_div] using hasSum_zeta_two

private lemma sum_range_succ_inv_sq_eq_sum_Icc (N : ℕ) :
    (∑ q ∈ Finset.range (N + 1), (((q : ℝ) ^ 2)⁻¹)) =
      ∑ q ∈ Finset.Icc 1 N, (((q : ℝ) ^ 2)⁻¹) := by
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := Ioc_zero_eq_Icc_one N
  rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc,
    Finset.Icc_eq_cons_Ioc (Nat.zero_le N)]
  simp [hIoc]

private lemma basel_partial_bounds {N : ℕ} (hN : 1 ≤ N) :
    let P := ∑ q ∈ Finset.Icc 1 N, (((q : ℝ) ^ 2)⁻¹)
    P ≤ Real.pi ^ 2 / 6 ∧ Real.pi ^ 2 / 6 ≤ P + ((N : ℝ)⁻¹) := by
  classical
  let f : ℕ → ℝ := fun n => (((n : ℝ) ^ 2)⁻¹)
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    positivity
  have hf_hasSum : HasSum f (Real.pi ^ 2 / 6) := by
    simpa [f] using hasSum_one_div_nat_sq
  let P : ℝ := ∑ q ∈ Finset.Icc 1 N, f q
  have hP_range : (∑ q ∈ Finset.range (N + 1), f q) = P := by
    dsimp [P, f]
    exact sum_range_succ_inv_sq_eq_sum_Icc N
  have hlower : P ≤ Real.pi ^ 2 / 6 := by
    exact sum_le_hasSum (Finset.Icc 1 N) (fun q _hq => hf_nonneg q) hf_hasSum
  have hbound_range : ∀ r : ℕ, (∑ q ∈ Finset.range r, f q) ≤ P + ((N : ℝ)⁻¹) := by
    intro r
    by_cases hr : r ≤ N + 1
    · have hsubset : Finset.range r ⊆ Finset.range (N + 1) := by
        intro q hq
        exact Finset.mem_range.mpr ((Finset.mem_range.mp hq).trans_le hr)
      have hle : (∑ q ∈ Finset.range r, f q) ≤ ∑ q ∈ Finset.range (N + 1), f q := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun q _hq _hnot => hf_nonneg q)
      calc
        (∑ q ∈ Finset.range r, f q) ≤ P := by simpa [hP_range] using hle
        _ ≤ P + ((N : ℝ)⁻¹) := by
          have hnonneg : 0 ≤ ((N : ℝ)⁻¹) := by positivity
          linarith
    · have hrle : N + 1 ≤ r := Nat.le_of_not_ge hr
      have htail_subset : Finset.Ico (N + 1) r ⊆ Finset.Ioc N r := by
        intro q hq
        simp only [Finset.mem_Ico, Finset.mem_Ioc] at hq ⊢
        omega
      have htail_le_Ioc :
          (∑ q ∈ Finset.Ico (N + 1) r, f q) ≤
            ∑ q ∈ Finset.Ioc N r, f q := by
        exact Finset.sum_le_sum_of_subset_of_nonneg htail_subset
          (fun q _hq _hnot => hf_nonneg q)
      have htail_Ioc :
          (∑ q ∈ Finset.Ioc N r, f q) ≤ ((N : ℝ)⁻¹) - ((r : ℝ)⁻¹) := by
        simpa [f] using
          (sum_Ioc_inv_sq_le_sub (α := ℝ) (k := N) (n := r)
            (Nat.ne_of_gt hN) (by omega))
      have htail_le :
          (∑ q ∈ Finset.Ico (N + 1) r, f q) ≤ ((N : ℝ)⁻¹) := by
        have hr_nonneg : 0 ≤ ((r : ℝ)⁻¹) := by positivity
        exact htail_le_Ioc.trans (htail_Ioc.trans (by linarith))
      calc
        (∑ q ∈ Finset.range r, f q)
            = (∑ q ∈ Finset.range (N + 1), f q) +
                ∑ q ∈ Finset.Ico (N + 1) r, f q := by
              rw [Finset.sum_range_add_sum_Ico _ hrle]
        _ ≤ P + ((N : ℝ)⁻¹) := by
              nlinarith [hP_range, htail_le]
  have hupper :
      Real.pi ^ 2 / 6 ≤ P + ((N : ℝ)⁻¹) := by
    have htsum_le := Real.tsum_le_of_sum_range_le hf_nonneg hbound_range
    simpa [hf_hasSum.tsum_eq] using htsum_le
  exact ⟨hlower, hupper⟩

private lemma triangular_error_of_floor {y j : ℝ} (hy1 : 1 ≤ y) (hj0 : 0 ≤ j)
    (hj_le : j ≤ y) (hy_lt : y < j + 1) :
    |j * (j + 1) / 2 - y ^ 2 / 2| ≤ 2 * y := by
  have hy0 : 0 ≤ y := zero_le_one.trans hy1
  have hy_le_j1 : y ≤ j + 1 := hy_lt.le
  have hdiff_nonneg : 0 ≤ y - j := sub_nonneg.mpr hj_le
  have hdiff_le : y - j ≤ 1 := by linarith
  have hj1_nonneg : 0 ≤ j + 1 := by nlinarith
  have hj1_le : j + 1 ≤ 2 * y := by nlinarith
  have hprod_le : (y - j) * (j + 1) ≤ 1 * (2 * y) :=
    mul_le_mul hdiff_le hj1_le hj1_nonneg (by norm_num)
  have hsq_le_yj : y ^ 2 ≤ y * (j + 1) := by
    have := mul_nonneg hy0 (sub_nonneg.mpr hy_le_j1)
    nlinarith
  have hlow_aux : y ^ 2 - j * (j + 1) ≤ (y - j) * (j + 1) := by
    nlinarith
  have hlow : y ^ 2 / 2 - j * (j + 1) / 2 ≤ 2 * y := by
    nlinarith
  have hsq_j_le_y : j ^ 2 ≤ y ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hj_le) (add_nonneg hy0 hj0)
    nlinarith
  have hupper : j * (j + 1) / 2 - y ^ 2 / 2 ≤ 2 * y := by
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

private lemma triangular_term_error {N q : ℕ} (hq : 1 ≤ q) (hqN : q ≤ N) :
    |((N / q : ℕ) : ℝ) * (((N / q : ℕ) : ℝ) + 1) / 2 -
        ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)| ≤
      2 * (N : ℝ) * ((q : ℝ)⁻¹) := by
  let y : ℝ := (N : ℝ) / (q : ℝ)
  let j : ℝ := ((N / q : ℕ) : ℝ)
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq_ne : (q : ℝ) ≠ 0 := hq_pos.ne'
  have hj0 : 0 ≤ j := by dsimp [j]; positivity
  have hj_le : j ≤ y := by
    dsimp [j, y]
    exact Nat.cast_div_le
  have hy_lt : y < j + 1 := by
    have hfloor :
        Nat.floor ((N : ℝ) / (q : ℝ)) = N / q := by
      simpa using (Nat.floor_div_eq_div (K := ℝ) N q)
    dsimp [y, j]
    simpa [hfloor] using Nat.lt_floor_add_one ((N : ℝ) / (q : ℝ))
  have hy1 : 1 ≤ y := by
    have hqN_real : (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hqN
    have hmul : (1 : ℝ) * (q : ℝ) ≤ y * (q : ℝ) := by
      dsimp [y]
      field_simp [hq_ne]
      exact hqN_real
    exact (mul_le_mul_iff_right₀ hq_pos).mp (by simpa [mul_comm] using hmul)
  have h := triangular_error_of_floor hy1 hj0 hj_le hy_lt
  dsimp [y, j] at h
  have hquad :
      ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹) =
        ((N : ℝ) / (q : ℝ)) ^ 2 / 2 := by
    field_simp [hq_ne]
  have hrhs :
      2 * (N : ℝ) * ((q : ℝ)⁻¹) = 2 * ((N : ℝ) / (q : ℝ)) := by
    field_simp [hq_ne]
  simpa [hquad, hrhs] using h

private lemma harmonic_sum_Icc_inv (N : ℕ) :
    (∑ q ∈ Finset.Icc 1 N, ((q : ℝ)⁻¹)) = (harmonic N : ℝ) := by
  have h :
      ((harmonic N : ℚ) : ℝ) =
        ∑ q ∈ Finset.Icc 1 N, ((q : ℝ)⁻¹) := by
    simp [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact h.symm

private lemma log_two_mul_nat_ge_half {N : ℕ} (hN : 1 ≤ N) :
    (1 / 2 : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have harg : (2 : ℝ) ≤ 2 * (N : ℝ) := by
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  exact hlog2.trans (Real.log_le_log (by norm_num) harg)

private lemma log_two_mul_ge_half {x : ℝ} (hx : 1 ≤ x) :
    (1 / 2 : ℝ) ≤ Real.log (2 * x) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have harg : (2 : ℝ) ≤ 2 * x := by nlinarith
  exact hlog2.trans (Real.log_le_log (by norm_num) harg)

private lemma one_add_log_nat_le_three_log_two_mul {N : ℕ} (hN : 1 ≤ N) :
    1 + Real.log (N : ℝ) ≤ 3 * Real.log (2 * (N : ℝ)) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have harg : (N : ℝ) ≤ 2 * (N : ℝ) := by nlinarith [show (0 : ℝ) ≤ N by positivity]
  have hlog_le : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log hNpos harg
  have hhalf := log_two_mul_nat_ge_half hN
  nlinarith

private lemma triangular_summatory_error {N : ℕ} (hN : 1 ≤ N) :
    |(∑ q ∈ Finset.Icc 1 N,
        ((N / q : ℕ) : ℝ) * (((N / q : ℕ) : ℝ) + 1) / 2) -
      ∑ q ∈ Finset.Icc 1 N,
        ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)| ≤
      6 * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
  classical
  let T : ℕ → ℝ := fun q =>
    ((N / q : ℕ) : ℝ) * (((N / q : ℕ) : ℝ) + 1) / 2
  let Q : ℕ → ℝ := fun q =>
    ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)
  have hterm :
      |(∑ q ∈ Finset.Icc 1 N, T q) - ∑ q ∈ Finset.Icc 1 N, Q q| ≤
        ∑ q ∈ Finset.Icc 1 N, 2 * (N : ℝ) * ((q : ℝ)⁻¹) := by
    calc
      |(∑ q ∈ Finset.Icc 1 N, T q) - ∑ q ∈ Finset.Icc 1 N, Q q|
          = |∑ q ∈ Finset.Icc 1 N, (T q - Q q)| := by
              rw [Finset.sum_sub_distrib]
      _ ≤ ∑ q ∈ Finset.Icc 1 N, |T q - Q q| :=
              Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Finset.Icc 1 N, 2 * (N : ℝ) * ((q : ℝ)⁻¹) := by
              refine Finset.sum_le_sum ?_
              intro q hq
              have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
              have hqN : q ≤ N := (Finset.mem_Icc.mp hq).2
              simpa [T, Q] using triangular_term_error (N := N) (q := q) hq1 hqN
  have hfactor :
      (∑ q ∈ Finset.Icc 1 N, 2 * (N : ℝ) * ((q : ℝ)⁻¹)) =
        2 * (N : ℝ) * (harmonic N : ℝ) := by
    rw [← harmonic_sum_Icc_inv N]
    exact (Finset.mul_sum (s := Finset.Icc 1 N)
      (a := 2 * (N : ℝ)) (f := fun q => ((q : ℝ)⁻¹))).symm
  have hH : (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) :=
    harmonic_le_one_add_log N
  have hlog := one_add_log_nat_le_three_log_two_mul hN
  calc
    |(∑ q ∈ Finset.Icc 1 N, T q) - ∑ q ∈ Finset.Icc 1 N, Q q|
        ≤ ∑ q ∈ Finset.Icc 1 N, 2 * (N : ℝ) * ((q : ℝ)⁻¹) := hterm
    _ = 2 * (N : ℝ) * (harmonic N : ℝ) := hfactor
    _ ≤ 2 * (N : ℝ) * (1 + Real.log (N : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ 6 * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
          have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * (N : ℝ))
          nlinarith

private lemma basel_weighted_error {N : ℕ} (hN : 1 ≤ N) :
    |(∑ q ∈ Finset.Icc 1 N,
        ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)) -
      (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| ≤ (N : ℝ) / 2 := by
  classical
  let P : ℝ := ∑ q ∈ Finset.Icc 1 N, (((q : ℝ) ^ 2)⁻¹)
  let C : ℝ := (N : ℝ) ^ 2 / 2
  have hb := basel_partial_bounds (N := N) hN
  dsimp only at hb
  have hP_le : P ≤ Real.pi ^ 2 / 6 := by
    simpa [P] using hb.1
  have htail : Real.pi ^ 2 / 6 - P ≤ ((N : ℝ)⁻¹) := by
    have h := hb.2
    simpa [P] using (sub_le_iff_le_add'.mpr h)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hsum :
      (∑ q ∈ Finset.Icc 1 N,
        ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)) = C * P := by
    dsimp [C, P]
    exact (Finset.mul_sum (s := Finset.Icc 1 N)
      (a := (N : ℝ) ^ 2 / 2) (f := fun q => (((q : ℝ) ^ 2)⁻¹))).symm
  have htarget : (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 = C * (Real.pi ^ 2 / 6) := by
    dsimp [C]
    ring
  have hnonpos : C * P - C * (Real.pi ^ 2 / 6) ≤ 0 := by
    exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left hP_le hC_nonneg)
  calc
    |(∑ q ∈ Finset.Icc 1 N,
        ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)) -
      (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2|
        = |C * P - C * (Real.pi ^ 2 / 6)| := by rw [hsum, htarget]
    _ = C * (Real.pi ^ 2 / 6 - P) := by
          rw [abs_of_nonpos hnonpos]
          ring
    _ ≤ C * ((N : ℝ)⁻¹) := by
          exact mul_le_mul_of_nonneg_left htail hC_nonneg
    _ = (N : ℝ) / 2 := by
          have hNpos : (N : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hN)
          dsimp [C]
          field_simp [hNpos]

private lemma sigma_summatory_nat_bound {N : ℕ} (hN : 1 ≤ N) :
    |(∑ m ∈ Finset.Icc 1 N, sigmaR m) -
      (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| ≤
      7 * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
  classical
  let T : ℕ → ℝ := fun q =>
    ((N / q : ℕ) : ℝ) * (((N / q : ℕ) : ℝ) + 1) / 2
  let Q : ℕ → ℝ := fun q =>
    ((N : ℝ) ^ 2 / 2) * (((q : ℝ) ^ 2)⁻¹)
  have htri := triangular_summatory_error (N := N) hN
  have hbasel := basel_weighted_error (N := N) hN
  have hhalf :
      (N : ℝ) / 2 ≤ (N : ℝ) * Real.log (2 * (N : ℝ)) := by
    have hlog := log_two_mul_nat_ge_half hN
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (N : ℝ))
    nlinarith
  calc
    |(∑ m ∈ Finset.Icc 1 N, sigmaR m) -
      (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2|
        = |(∑ q ∈ Finset.Icc 1 N, T q) -
            (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| := by
              rw [sigma_summatory_eq_triangular]
    _ ≤ |(∑ q ∈ Finset.Icc 1 N, T q) - ∑ q ∈ Finset.Icc 1 N, Q q| +
          |(∑ q ∈ Finset.Icc 1 N, Q q) -
            (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| :=
          abs_sub_le _ _ _
    _ ≤ 7 * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
          have htri' : |(∑ q ∈ Finset.Icc 1 N, T q) - ∑ q ∈ Finset.Icc 1 N, Q q| ≤
              6 * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
            simpa [T, Q] using htri
          have hbasel' : |(∑ q ∈ Finset.Icc 1 N, Q q) -
              (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| ≤ (N : ℝ) / 2 := by
            simpa [Q] using hbasel
          nlinarith [htri', hbasel', hhalf]

private lemma floor_quadratic_error {x : ℝ} (hx : 1 ≤ x) :
    |(Real.pi ^ 2 / 12) * (⌊x⌋₊ : ℝ) ^ 2 -
      (Real.pi ^ 2 / 12) * x ^ 2| ≤
      Real.pi ^ 2 * x * Real.log (2 * x) := by
  let N : ℕ := ⌊x⌋₊
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hN_le : (N : ℝ) ≤ x := by
    dsimp [N]
    exact Nat.floor_le hx0
  have hx_lt : x < (N : ℝ) + 1 := by
    dsimp [N]
    exact Nat.lt_floor_add_one x
  have hdiff_nonneg : 0 ≤ x - (N : ℝ) := sub_nonneg.mpr hN_le
  have hdiff_le : x - (N : ℝ) ≤ 1 := by linarith
  have hsum_nonneg : 0 ≤ x + (N : ℝ) := by positivity
  have hsum_le : x + (N : ℝ) ≤ 2 * x := by nlinarith
  have hsquares : x ^ 2 - (N : ℝ) ^ 2 ≤ 2 * x := by
    have hmul : (x - (N : ℝ)) * (x + (N : ℝ)) ≤ 1 * (2 * x) :=
      mul_le_mul hdiff_le hsum_le hsum_nonneg (by norm_num)
    nlinarith
  have hsquares_nonneg : 0 ≤ x ^ 2 - (N : ℝ) ^ 2 := by
    have hmul_nonneg := mul_nonneg (sub_nonneg.mpr hN_le) (add_nonneg hx0 (by positivity))
    nlinarith
  have hconst_nonneg : 0 ≤ Real.pi ^ 2 / 12 := by positivity
  have hbasic :
      |(Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 -
        (Real.pi ^ 2 / 12) * x ^ 2| ≤
        2 * (Real.pi ^ 2 / 12) * x := by
    have hnonpos :
        (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 -
          (Real.pi ^ 2 / 12) * x ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg hconst_nonneg hsquares_nonneg]
    rw [abs_of_nonpos hnonpos]
    have hmul := mul_le_mul_of_nonneg_left hsquares hconst_nonneg
    nlinarith
  have hlog := log_two_mul_ge_half hx
  have hpi_x_nonneg : 0 ≤ Real.pi ^ 2 * x := by positivity
  have hlogmul := mul_le_mul_of_nonneg_left hlog hpi_x_nonneg
  exact hbasic.trans (by nlinarith)

theorem sigma_summatory_asymptotic :
    ∃ K, 0 < K ∧ ∀ x : ℝ, 1 ≤ x →
      |(∑ m ∈ Finset.Icc 1 ⌊x⌋₊, sigmaR m) -
        (Real.pi ^ 2 / 12) * x ^ 2| ≤ K * x * Real.log (2 * x) := by
  refine ⟨8 + Real.pi ^ 2, by positivity, ?_⟩
  intro x hx
  let N : ℕ := ⌊x⌋₊
  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.floor_pos.mpr hx
  have hN : 1 ≤ N := hNpos
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hN_le_x : (N : ℝ) ≤ x := by
    dsimp [N]
    exact Nat.floor_le hx0
  have hlogN_nonneg : 0 ≤ Real.log (2 * (N : ℝ)) := by
    have hhalf := log_two_mul_nat_ge_half hN
    linarith
  have hlog_mono :
      Real.log (2 * (N : ℝ)) ≤ Real.log (2 * x) := by
    have harg_pos : 0 < 2 * (N : ℝ) := by positivity
    have harg_le : 2 * (N : ℝ) ≤ 2 * x := by nlinarith
    exact Real.log_le_log harg_pos harg_le
  have hNxlog :
      (N : ℝ) * Real.log (2 * (N : ℝ)) ≤ x * Real.log (2 * x) := by
    exact mul_le_mul hN_le_x hlog_mono hlogN_nonneg hx0
  have hnat := sigma_summatory_nat_bound (N := N) hN
  have hnat_x :
      |(∑ m ∈ Finset.Icc 1 N, sigmaR m) -
        (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| ≤
        7 * x * Real.log (2 * x) := by
    have hmul := mul_le_mul_of_nonneg_left hNxlog (by norm_num : (0 : ℝ) ≤ 7)
    nlinarith [hnat, hmul]
  have hfloor := floor_quadratic_error (x := x) hx
  have hxlog_nonneg : 0 ≤ x * Real.log (2 * x) := by
    have hhalf := log_two_mul_ge_half hx
    exact mul_nonneg hx0 (by linarith)
  calc
    |(∑ m ∈ Finset.Icc 1 ⌊x⌋₊, sigmaR m) -
        (Real.pi ^ 2 / 12) * x ^ 2|
        = |(∑ m ∈ Finset.Icc 1 N, sigmaR m) -
            (Real.pi ^ 2 / 12) * x ^ 2| := by rfl
    _ ≤ |(∑ m ∈ Finset.Icc 1 N, sigmaR m) -
          (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| +
        |(Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 -
          (Real.pi ^ 2 / 12) * x ^ 2| :=
          abs_sub_le _ _ _
    _ ≤ (8 + Real.pi ^ 2) * x * Real.log (2 * x) := by
          have hfloor' :
              |(Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 -
                (Real.pi ^ 2 / 12) * x ^ 2| ≤
                Real.pi ^ 2 * x * Real.log (2 * x) := by
            simpa [N] using hfloor
          nlinarith [hnat_x, hfloor', hxlog_nonneg]

end
end AnalyticCombinatorics.Ch8.Partitions.Sigma
end

section
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

lemma C_pos : 0 < C := by
  dsimp [C]
  positivity

lemma sigmaR_nonneg (n : ℕ) : 0 ≤ Sigma.sigmaR n := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  exact Finset.sum_nonneg fun d _hd => by positivity

lemma sigmaR_le_square {n : ℕ} (hn : 1 ≤ n) :
    Sigma.sigmaR n ≤ (n : ℝ) ^ 2 := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    have hmem := (Nat.mem_divisors.mp hd)
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hmem.1 (Nat.pos_of_ne_zero hmem.2)
    have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hmem.2) hmem.1
    exact Finset.mem_Icc.mpr ⟨hdpos, hdle⟩
  have hcard_nat : n.divisors.card ≤ n := by
    calc
      n.divisors.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
      _ = n := by
        simp
  have hsum_le :
      (∑ d ∈ n.divisors, (d : ℝ)) ≤ ∑ _d ∈ n.divisors, (n : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    have hmem := (Nat.mem_divisors.mp hd)
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hmem.2) hmem.1
  calc
    (∑ d ∈ n.divisors, (d : ℝ))
        ≤ ∑ _d ∈ n.divisors, (n : ℝ) := hsum_le
    _ = (n.divisors.card : ℝ) * (n : ℝ) := by
          simp [nsmul_eq_mul, mul_comm]
    _ ≤ (n : ℝ) ^ 2 := by
          have hcard : (n.divisors.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard_nat
          have hn0 : 0 ≤ (n : ℝ) := by positivity
          nlinarith

lemma sigma_summatory_quadratic_bound :
    ∃ B : ℝ, 0 < B ∧
      ∀ N : ℕ, (∑ m ∈ Finset.Icc 1 N, Sigma.sigmaR m) ≤ B * (N : ℝ) ^ 2 := by
  rcases Sigma.sigma_summatory_asymptotic with ⟨K, hKpos, hK⟩
  refine ⟨Real.pi ^ 2 / 12 + 2 * K + 1, by positivity, ?_⟩
  intro N
  by_cases hN : 1 ≤ N
  · have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have hKbound := hK (N : ℝ) hNR
    have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
    have hmain_nonneg : 0 ≤ (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 := by positivity
    have hlog_le : Real.log (2 * (N : ℝ)) ≤ 2 * (N : ℝ) := by
      exact Real.log_le_self (by positivity : 0 ≤ 2 * (N : ℝ))
    have hlog_term :
        K * (N : ℝ) * Real.log (2 * (N : ℝ)) ≤
          2 * K * (N : ℝ) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hlog_le (by positivity : 0 ≤ K * (N : ℝ))
      nlinarith
    have hupper :
        (∑ m ∈ Finset.Icc 1 N, Sigma.sigmaR m) ≤
          (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 +
            K * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
      have hle_abs :
          (∑ m ∈ Finset.Icc 1 N, Sigma.sigmaR m) -
              (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 ≤
            |(∑ m ∈ Finset.Icc 1 N, Sigma.sigmaR m) -
              (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| :=
        le_abs_self _
      have hKbound' :
          |(∑ m ∈ Finset.Icc 1 N, Sigma.sigmaR m) -
              (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2| ≤
            K * (N : ℝ) * Real.log (2 * (N : ℝ)) := by
        simpa [hfloor] using hKbound
      linarith
    calc
      (∑ m ∈ Finset.Icc 1 N, Sigma.sigmaR m)
          ≤ (Real.pi ^ 2 / 12) * (N : ℝ) ^ 2 +
              K * (N : ℝ) * Real.log (2 * (N : ℝ)) := hupper
      _ ≤ (Real.pi ^ 2 / 12 + 2 * K) * (N : ℝ) ^ 2 := by
            nlinarith [hlog_term]
      _ ≤ (Real.pi ^ 2 / 12 + 2 * K + 1) * (N : ℝ) ^ 2 := by
            have hN2 : 0 ≤ (N : ℝ) ^ 2 := by positivity
            nlinarith
  · have hN0 : N = 0 := by omega
    subst hN0
    simp

lemma erdosWeight_nonneg_of_mem {n m : ℕ} (hm : m ∈ Finset.Icc 1 (n - 1)) :
    0 ≤ erdosWeight n m := by
  have hmI := Finset.mem_Icc.mp hm
  exact erdosWeight_nonneg_of_lt (n := n) (m := m) (by omega)

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

section
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

open Filter
open scoped BigOperators Topology Interval

noncomputable section

local notation "σR" => Sigma.sigmaR

def blockIndex (n m : ℕ) : ℕ :=
  ⌊(m : ℝ) / Real.sqrt (n : ℝ)⌋₊

def numBlocks (n : ℕ) : ℕ :=
  ⌊((n - 1 : ℕ) : ℝ) / Real.sqrt (n : ℝ)⌋₊ + 1

lemma blockIndex_lt_numBlocks {n m : ℕ} (hm : m ∈ Finset.Icc 1 (n - 1)) :
    blockIndex n m < numBlocks n := by
  have hm_le : m ≤ n - 1 := (Finset.mem_Icc.mp hm).2
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hdiv_le :
      (m : ℝ) / Real.sqrt (n : ℝ) ≤
        ((n - 1 : ℕ) : ℝ) / Real.sqrt (n : ℝ) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hm_le) hsqrt_nonneg
  have hfloor_le :
      ⌊(m : ℝ) / Real.sqrt (n : ℝ)⌋₊ ≤
        ⌊((n - 1 : ℕ) : ℝ) / Real.sqrt (n : ℝ)⌋₊ := by
    exact Nat.floor_mono hdiv_le
  dsimp [blockIndex, numBlocks]
  omega

lemma block_decomposition (n : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 (n - 1), f m) =
      ∑ k ∈ Finset.range (numBlocks n),
        ∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m := by
  classical
  exact (Finset.sum_fiberwise_of_maps_to
    (s := Finset.Icc 1 (n - 1))
    (t := Finset.range (numBlocks n))
    (g := blockIndex n)
    (f := f)
    (fun m hm => Finset.mem_range.mpr (blockIndex_lt_numBlocks hm))).symm

lemma block_subset_Icc_floor_succ_sqrt {n k m : ℕ}
    (hm : m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k)) :
    m ∈ Finset.Icc 1 ⌊((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)⌋₊ := by
  have hmI : m ∈ Finset.Icc 1 (n - 1) := (Finset.mem_filter.mp hm).1
  have hmk : blockIndex n m = k := (Finset.mem_filter.mp hm).2
  have hm_ge : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
  have hx_nonneg : 0 ≤ (m : ℝ) / Real.sqrt (n : ℝ) := by positivity
  have hfloor_lt :
      (m : ℝ) / Real.sqrt (n : ℝ) < (k : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((m : ℝ) / Real.sqrt (n : ℝ))
    have hfloor_eq : ⌊(m : ℝ) / Real.sqrt (n : ℝ)⌋₊ = k := by
      simpa [blockIndex] using hmk
    simpa [hfloor_eq, Nat.cast_add, Nat.cast_one] using h
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hm_lt :
      (m : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hfloor_lt.le hsqrt_nonneg
    have hleft :
        ((m : ℝ) / Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) = (m : ℝ) := by
      by_cases hn : n = 0
      · subst hn
        have hm0 : m = 0 := by
          have hmle : m ≤ 0 := (Finset.mem_Icc.mp hmI).2
          omega
        simp [hm0]
      · have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := by
          exact (Real.sqrt_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)).ne'
        field_simp [hsqrt_ne]
    have hright :
        ((k : ℝ) + 1) * Real.sqrt (n : ℝ) =
          ((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ) := by
      norm_num
    simpa [hleft, hright] using hmul
  refine Finset.mem_Icc.mpr ⟨hm_ge, ?_⟩
  exact Nat.le_floor hm_lt

lemma sigma_block_le_floor_succ_sqrt (n k : ℕ) :
    (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), σR m) ≤
      ∑ m ∈ Finset.Icc 1 ⌊((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)⌋₊, σR m := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun m hm => block_subset_Icc_floor_succ_sqrt (n := n) (k := k) hm)
    (fun m _hm _hnot => Erdos.sigmaR_nonneg m)

lemma sigma_summatory_quadratic_bound_real :
    ∃ B : ℝ, 0 < B ∧
      ∀ x : ℝ, 1 ≤ x →
        (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, σR m) ≤ B * x ^ 2 := by
  rcases Erdos.sigma_summatory_quadratic_bound with ⟨B, hBpos, hB⟩
  refine ⟨B, hBpos, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hsq_le : (⌊x⌋₊ : ℝ) ^ 2 ≤ x ^ 2 := by
    exact (sq_le_sq₀ (by positivity : 0 ≤ (⌊x⌋₊ : ℝ)) hx0).mpr hfloor_le
  exact (hB ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left hsq_le hBpos.le)

def sigmaQuadConst : ℝ :=
  Classical.choose sigma_summatory_quadratic_bound_real

lemma sigmaQuadConst_pos : 0 < sigmaQuadConst :=
  (Classical.choose_spec sigma_summatory_quadratic_bound_real).1

lemma sigma_summatory_le_quad_real {x : ℝ} (hx : 1 ≤ x) :
    (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, σR m) ≤ sigmaQuadConst * x ^ 2 :=
  (Classical.choose_spec sigma_summatory_quadratic_bound_real).2 x hx

lemma sigma_block_le_const (n k : ℕ) :
      (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), σR m) ≤
        sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ) := by
  have hx1 : 1 ≤ ((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ) ∨
      ((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ) < 1 := le_or_gt 1 _
  rcases hx1 with hx1 | hxlt
  · have hsum := sigma_block_le_floor_succ_sqrt (n := n) (k := k)
    have hquad :=
      sigma_summatory_le_quad_real
        (x := ((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) hx1
    have hpow :
        (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) ^ 2 =
          ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
    calc
      (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), σR m)
          ≤ ∑ m ∈ Finset.Icc 1 ⌊((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)⌋₊, σR m := hsum
      _ ≤ sigmaQuadConst * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) ^ 2 := hquad
      _ = sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ) := by rw [hpow]; ring
  · have hfilter_empty :
        (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k) = ∅ := by
      ext m
      constructor
      · intro hm
        have hsub := block_subset_Icc_floor_succ_sqrt (n := n) (k := k) hm
        have hfloor0 : ⌊((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)⌋₊ = 0 := by
          exact Nat.floor_eq_zero.mpr hxlt
        have hmI := Finset.mem_Icc.mp hsub
        omega
      · intro hm
        simp at hm
    simpa [hfilter_empty] using
      (show 0 ≤ sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ) by
        exact mul_nonneg
          (mul_nonneg sigmaQuadConst_pos.le (sq_nonneg _))
          (by positivity))

lemma sqrt_drop_ge_half_scale {n m : ℕ} (hn : 0 < n) (hmn : m ≤ n) :
    (m : ℝ) / (2 * Real.sqrt (n : ℝ)) ≤
      Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ) := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hsub0 : 0 ≤ ((n - m : ℕ) : ℝ) := by positivity
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos_of_pos (by exact_mod_cast hn)
  have hsqrt_sub_le :
      Real.sqrt ((n - m : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n m)
  have hdrop_nonneg :
      0 ≤ Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ) := by
    exact sub_nonneg.mpr hsqrt_sub_le
  have hsum_le :
      Real.sqrt (n : ℝ) + Real.sqrt ((n - m : ℕ) : ℝ) ≤
        2 * Real.sqrt (n : ℝ) := by
    nlinarith
  have hidentity :
      (m : ℝ) =
        (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)) *
          (Real.sqrt (n : ℝ) + Real.sqrt ((n - m : ℕ) : ℝ)) := by
    calc
      (m : ℝ)
          = (n : ℝ) - ((n - m : ℕ) : ℝ) := by
              rw [Nat.cast_sub hmn]
              ring
      _ = Real.sqrt (n : ℝ) ^ 2 - Real.sqrt ((n - m : ℕ) : ℝ) ^ 2 := by
              rw [Real.sq_sqrt hn0, Real.sq_sqrt hsub0]
      _ =
        (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)) *
          (Real.sqrt (n : ℝ) + Real.sqrt ((n - m : ℕ) : ℝ)) := by
              ring
  have hmul :
      (m : ℝ) ≤
        (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)) *
          (2 * Real.sqrt (n : ℝ)) := by
    rw [hidentity]
    exact mul_le_mul_of_nonneg_left hsum_le hdrop_nonneg
  exact (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (n : ℝ))).mpr hmul

lemma erdosWeight_le_model_left_half {n m : ℕ}
    (hn : 0 < n) (hmn : m < n) (hmhalf : 2 * m ≤ n) :
    erdosWeight n m ≤
      (2 / (n : ℝ)) * σR m *
        Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) := by
  have hn_pos_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden_pos_nat : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hden_pos : 0 < ((n - m : ℕ) : ℝ) := by exact_mod_cast hden_pos_nat
  have hden_ge_half : (n : ℝ) / 2 ≤ ((n - m : ℕ) : ℝ) := by
    have hmnle : m ≤ n := le_of_lt hmn
    rw [Nat.cast_sub hmnle]
    nlinarith [show (2 : ℝ) * (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmhalf]
  have hrecip :
      (1 : ℝ) / ((n - m : ℕ) : ℝ) ≤ 2 / (n : ℝ) := by
    calc
      (1 : ℝ) / ((n - m : ℕ) : ℝ)
          ≤ 1 / ((n : ℝ) / 2) :=
            one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) / 2) hden_ge_half
      _ = 2 / (n : ℝ) := by
            field_simp [hn_pos_real.ne']
  have hdrop :=
    sqrt_drop_ge_half_scale (n := n) (m := m) hn (le_of_lt hmn)
  have hexp :
      Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) ≤
        Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hCnonneg : 0 ≤ C := C_pos.le
    have hCmul := mul_le_mul_of_nonneg_left hdrop hCnonneg
    have hscale :
        C * ((m : ℝ) / (2 * Real.sqrt (n : ℝ))) =
          (C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ)) := by
      ring
    nlinarith
  have hsig_nonneg : 0 ≤ σR m := Erdos.sigmaR_nonneg m
  have hexp_nonneg :
      0 ≤ Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) :=
    (Real.exp_pos _).le
  calc
    erdosWeight n m
        = σR m * ((1 : ℝ) / ((n - m : ℕ) : ℝ)) *
            Real.exp (-C *
              (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) := by
            rw [erdosWeight]
            ring
    _ ≤ σR m * (2 / (n : ℝ)) *
            Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hrecip hsig_nonneg)
            hexp
            (Real.exp_pos _).le
            (mul_nonneg hsig_nonneg (by positivity : 0 ≤ 2 / (n : ℝ)))
    _ = (2 / (n : ℝ)) * σR m *
            Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) := by
          ring

lemma blockIndex_le_ratio (n m : ℕ) :
    (blockIndex n m : ℝ) ≤ (m : ℝ) / Real.sqrt (n : ℝ) := by
  dsimp [blockIndex]
  exact Nat.floor_le (by positivity : 0 ≤ (m : ℝ) / Real.sqrt (n : ℝ))

lemma model_exp_le_block_exp {n m k : ℕ} (hmk : blockIndex n m = k) :
    Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) ≤
      Real.exp (-(C / 2) * (k : ℝ)) := by
  apply Real.exp_le_exp.mpr
  have hk_le : (k : ℝ) ≤ (m : ℝ) / Real.sqrt (n : ℝ) := by
    simpa [hmk] using blockIndex_le_ratio n m
  have hC2_nonneg : 0 ≤ C / 2 := by linarith [C_pos]
  nlinarith [mul_le_mul_of_nonneg_left hk_le hC2_nonneg]

lemma erdosWeight_le_block_model_left_half {n m k : ℕ}
    (hn : 0 < n)
    (hm : m ∈ (Finset.Icc 1 (n - 1)).filter
      (fun m => blockIndex n m = k ∧ 2 * m ≤ n)) :
    erdosWeight n m ≤
      (2 / (n : ℝ)) * σR m * Real.exp (-(C / 2) * (k : ℝ)) := by
  have hm_filter := Finset.mem_filter.mp hm
  have hmI : m ∈ Finset.Icc 1 (n - 1) := hm_filter.1
  have hmk : blockIndex n m = k := hm_filter.2.1
  have hmhalf : 2 * m ≤ n := hm_filter.2.2
  have hmn : m < n := by
    have hmle : m ≤ n - 1 := (Finset.mem_Icc.mp hmI).2
    omega
  have hbase := erdosWeight_le_model_left_half (n := n) (m := m) hn hmn hmhalf
  have hexp := model_exp_le_block_exp (n := n) (m := m) (k := k) hmk
  have hcoef_nonneg : 0 ≤ (2 / (n : ℝ)) * σR m := by
    exact mul_nonneg (by positivity) (Erdos.sigmaR_nonneg m)
  calc
    erdosWeight n m
        ≤ (2 / (n : ℝ)) * σR m *
            Real.exp (-(C / 2) * ((m : ℝ) / Real.sqrt (n : ℝ))) := hbase
    _ ≤ (2 / (n : ℝ)) * σR m * Real.exp (-(C / 2) * (k : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hexp hcoef_nonneg

lemma kernel_block_left_half_le (n k : ℕ) (hn : 0 < n) :
    (∑ m ∈ (Finset.Icc 1 (n - 1)).filter
      (fun m => blockIndex n m = k ∧ 2 * m ≤ n), erdosWeight n m) ≤
      2 * sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 *
        Real.exp (-(C / 2) * (k : ℝ)) := by
  classical
  let s := (Finset.Icc 1 (n - 1)).filter
    (fun m => blockIndex n m = k ∧ 2 * m ≤ n)
  let t := (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k)
  have hs_le :
      (∑ m ∈ s, erdosWeight n m) ≤
        ∑ m ∈ s, (2 / (n : ℝ)) * σR m * Real.exp (-(C / 2) * (k : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro m hm
    exact erdosWeight_le_block_model_left_half (n := n) (m := m) (k := k) hn (by simpa [s] using hm)
  have hfactor :
      (∑ m ∈ s, (2 / (n : ℝ)) * σR m * Real.exp (-(C / 2) * (k : ℝ))) =
        ((2 / (n : ℝ)) * Real.exp (-(C / 2) * (k : ℝ))) *
          (∑ m ∈ s, σR m) := by
    simp [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]
  have hsubset : s ⊆ t := by
    intro m hm
    simp [s, t] at hm ⊢
    exact ⟨hm.1, hm.2.1⟩
  have hsigma_s_le_t :
      (∑ m ∈ s, σR m) ≤ ∑ m ∈ t, σR m := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun m _hm _hnot => Erdos.sigmaR_nonneg m)
  have hblock := sigma_block_le_const n k
  have hcoef_nonneg :
      0 ≤ (2 / (n : ℝ)) * Real.exp (-(C / 2) * (k : ℝ)) := by
    positivity
  have hmain :
      ((2 / (n : ℝ)) * Real.exp (-(C / 2) * (k : ℝ))) *
          (∑ m ∈ s, σR m) ≤
        ((2 / (n : ℝ)) * Real.exp (-(C / 2) * (k : ℝ))) *
          (sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ)) := by
    exact mul_le_mul_of_nonneg_left (hsigma_s_le_t.trans (by simpa [t] using hblock)) hcoef_nonneg
  calc
    (∑ m ∈ s, erdosWeight n m)
        ≤ ∑ m ∈ s, (2 / (n : ℝ)) * σR m *
            Real.exp (-(C / 2) * (k : ℝ)) := hs_le
    _ = ((2 / (n : ℝ)) * Real.exp (-(C / 2) * (k : ℝ))) *
          (∑ m ∈ s, σR m) := hfactor
    _ ≤ ((2 / (n : ℝ)) * Real.exp (-(C / 2) * (k : ℝ))) *
          (sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 * (n : ℝ)) := hmain
    _ = 2 * sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 *
          Real.exp (-(C / 2) * (k : ℝ)) := by
          field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn]

lemma sqrt_sub_le_nine_tenths_sqrt {n r : ℕ} (hr : 2 * r ≤ n) :
    Real.sqrt (r : ℝ) ≤ (9 / 10 : ℝ) * Real.sqrt (n : ℝ) := by
  have hr_nonneg : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hright_nonneg : 0 ≤ (9 / 10 : ℝ) * Real.sqrt (n : ℝ) := by positivity
  have hsq :
      Real.sqrt (r : ℝ) ^ 2 ≤
        ((9 / 10 : ℝ) * Real.sqrt (n : ℝ)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ (r : ℝ))]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
    norm_num
    nlinarith [show (2 : ℝ) * (r : ℝ) ≤ (n : ℝ) by exact_mod_cast hr]
  exact (sq_le_sq₀ hr_nonneg hright_nonneg).mp hsq

lemma sqrt_drop_ge_right_half {n m : ℕ}
    (hmn : m ≤ n) (hright : n < 2 * m) :
    (1 / 10 : ℝ) * Real.sqrt (n : ℝ) ≤
      Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ) := by
  have hsub_half : 2 * (n - m) ≤ n := by omega
  have hsqrt_le :=
    sqrt_sub_le_nine_tenths_sqrt (n := n) (r := n - m) hsub_half
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

lemma erdosWeight_le_right_half {n m : ℕ}
    (hm : m ∈ Finset.Icc 1 (n - 1)) (hright : n < 2 * m) :
    erdosWeight n m ≤
      (n : ℝ) ^ 2 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
  have hmI := Finset.mem_Icc.mp hm
  have hm_pos : 1 ≤ m := hmI.1
  have hmn : m < n := by omega
  have hmn_le : m ≤ n := le_of_lt hmn
  have hden_pos_nat : 0 < n - m := Nat.sub_pos_of_lt hmn
  have hden_pos : 0 < ((n - m : ℕ) : ℝ) := by exact_mod_cast hden_pos_nat
  have hden_ge_one : (1 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by
    exact_mod_cast hden_pos_nat
  have hsig := Erdos.sigmaR_le_square (n := m) hm_pos
  have hm_le_n_real : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn_le
  have hm_sq_le_n_sq : (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity : 0 ≤ (m : ℝ)) (by positivity : 0 ≤ (n : ℝ))).mpr hm_le_n_real
  have hsig_le_n_sq : σR m ≤ (n : ℝ) ^ 2 := hsig.trans hm_sq_le_n_sq
  have hfrac_le :
      σR m / ((n - m : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hfrac_le_sig : σR m / ((n - m : ℕ) : ℝ) ≤ σR m := by
      rw [div_le_iff₀ hden_pos]
      have hmul := mul_le_mul_of_nonneg_left hden_ge_one (Erdos.sigmaR_nonneg m)
      simpa [one_mul] using hmul
    exact hfrac_le_sig.trans hsig_le_n_sq
  have hdrop := sqrt_drop_ge_right_half (n := n) (m := m) hmn_le hright
  have hexp :
      Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) ≤
        Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hCmul := mul_le_mul_of_nonneg_left hdrop C_pos.le
    nlinarith
  have hfrac_nonneg :
      0 ≤ σR m / ((n - m : ℕ) : ℝ) :=
    div_nonneg (Erdos.sigmaR_nonneg m) hden_pos.le
  calc
    erdosWeight n m
        = σR m / ((n - m : ℕ) : ℝ) *
            Real.exp (-C *
              (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) := rfl
    _ ≤ (n : ℝ) ^ 2 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
          exact mul_le_mul hfrac_le hexp (Real.exp_pos _).le (by positivity)

lemma right_half_kernel_sum_le (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
      if n < 2 * m then erdosWeight n m else 0) ≤
      (n : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
  classical
  let Bn : ℝ := (n : ℝ) ^ 2 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ))
  have hterm :
      ∀ m ∈ Finset.Icc 1 (n - 1),
        (if n < 2 * m then erdosWeight n m else 0) ≤ Bn := by
    intro m hm
    by_cases hright : n < 2 * m
    · simpa [Bn, hright] using erdosWeight_le_right_half (n := n) (m := m) hm hright
    · have hBn_nonneg : 0 ≤ Bn := by
        dsimp [Bn]
        positivity
      simp [hright, hBn_nonneg]
  have hsum :
      (∑ m ∈ Finset.Icc 1 (n - 1),
        if n < 2 * m then erdosWeight n m else 0) ≤
        ∑ m ∈ Finset.Icc 1 (n - 1), Bn := by
    exact Finset.sum_le_sum hterm
  have hcard : ((Finset.Icc 1 (n - 1)).card : ℝ) ≤ (n : ℝ) := by
    have hcard_nat : (Finset.Icc 1 (n - 1)).card ≤ n := by
      have hsubset : Finset.Icc 1 (n - 1) ⊆ Finset.range n := by
        intro m hm
        have hmge : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hmle : m ≤ n - 1 := (Finset.mem_Icc.mp hm).2
        exact Finset.mem_range.mpr (by omega)
      have h := Finset.card_le_card hsubset
      rw [Finset.card_range] at h
      exact h
    exact_mod_cast hcard_nat
  calc
    (∑ m ∈ Finset.Icc 1 (n - 1),
      if n < 2 * m then erdosWeight n m else 0)
        ≤ ∑ m ∈ Finset.Icc 1 (n - 1), Bn := hsum
    _ = ((Finset.Icc 1 (n - 1)).card : ℝ) * Bn := by
          simp [Bn, nsmul_eq_mul]
    _ ≤ (n : ℝ) * Bn := by
          exact mul_le_mul_of_nonneg_right hcard (by dsimp [Bn]; positivity)
    _ = (n : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (n : ℝ)) := by
          dsimp [Bn]
          ring

def leftBlockMajorant (k : ℕ) : ℝ :=
  2 * sigmaQuadConst * ((k + 1 : ℕ) : ℝ) ^ 2 *
    Real.exp (-(C / 2) * (k : ℝ))

lemma leftBlockMajorant_nonneg (k : ℕ) : 0 ≤ leftBlockMajorant k := by
  dsimp [leftBlockMajorant]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) sigmaQuadConst_pos.le)
      (sq_nonneg _))
    (Real.exp_pos _).le

lemma exp_neg_half_C_nat_eq_pow (k : ℕ) :
    Real.exp (-(C / 2) * (k : ℝ)) =
      (Real.exp (-(C / 2))) ^ k := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma summable_leftBlockMajorant : Summable leftBlockMajorant := by
  let r : ℝ := Real.exp (-(C / 2))
  have hr_pos : 0 < r := by dsimp [r]; positivity
  have hr_lt_one : ‖r‖ < 1 := by
    have hneg : -(C / 2) < 0 := by linarith [C_pos]
    have h : Real.exp (-(C / 2)) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
    simpa [r, abs_of_pos hr_pos] using h
  have h2 : Summable fun k : ℕ => ((k : ℝ) ^ 2) * r ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr_lt_one
  have h1 : Summable fun k : ℕ => ((k : ℝ) ^ 1) * r ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr_lt_one
  have h0 : Summable fun k : ℕ => ((k : ℝ) ^ 0) * r ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hr_lt_one
  have hpoly :
      Summable fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ 2) * r ^ k := by
    have hsum := (h2.add (h1.mul_left 2)).add h0
    refine hsum.congr ?_
    intro k
    norm_num
    ring
  refine hpoly.mul_left (2 * sigmaQuadConst) |>.congr ?_
  intro k
  dsimp [leftBlockMajorant, r]
  rw [exp_neg_half_C_nat_eq_pow k]
  ring

lemma tail_block_index_ge {n K k m : ℕ} (hn : 0 < n)
    (hm : m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k))
    (htail : (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ)) :
    K ≤ k := by
  have hmk : blockIndex n m = k := (Finset.mem_filter.mp hm).2
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos_of_pos (by exact_mod_cast hn)
  have hK_le_ratio : (K : ℝ) ≤ (m : ℝ) / Real.sqrt (n : ℝ) := by
    rw [le_div_iff₀' hsqrt_pos]
    simpa [mul_comm] using htail
  have hratio_lt : (m : ℝ) / Real.sqrt (n : ℝ) < (k : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((m : ℝ) / Real.sqrt (n : ℝ))
    have hfloor_eq : ⌊(m : ℝ) / Real.sqrt (n : ℝ)⌋₊ = k := by
      simpa [blockIndex] using hmk
    simpa [hfloor_eq, Nat.cast_add, Nat.cast_one] using h
  have hK_lt : (K : ℝ) < (k : ℝ) + 1 := lt_of_le_of_lt hK_le_ratio hratio_lt
  exact Nat.le_of_lt_succ (by exact_mod_cast hK_lt)

lemma left_half_tail_sum_le_block_majorants (n K : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
      if (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ n
      then erdosWeight n m
      else 0) ≤
      ∑ k ∈ Finset.range (numBlocks n),
        if K ≤ k then leftBlockMajorant k else 0 := by
  classical
  let f : ℕ → ℝ := fun m =>
    if (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ n
    then erdosWeight n m
    else 0
  have hdecomp := block_decomposition n f
  rw [hdecomp]
  refine Finset.sum_le_sum ?_
  intro k hk
  by_cases hKk : K ≤ k
  · have hterm_le :
        ∀ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
          f m ≤ if 2 * m ≤ n then erdosWeight n m else 0 := by
      intro m hm
      have hmI : m ∈ Finset.Icc 1 (n - 1) := (Finset.mem_filter.mp hm).1
      by_cases hhalf : 2 * m ≤ n
      · by_cases htail : (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ)
        · simp [f, htail, hhalf]
        · simp [f, htail, hhalf, Erdos.erdosWeight_nonneg_of_mem hmI]
      · simp [f, hhalf]
    have hsum_le_half :
        (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m) ≤
          ∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
            if 2 * m ≤ n then erdosWeight n m else 0 := by
      exact Finset.sum_le_sum hterm_le
    have hhalf_eq :
        (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
            if 2 * m ≤ n then erdosWeight n m else 0) =
          ∑ m ∈ (Finset.Icc 1 (n - 1)).filter
            (fun m => blockIndex n m = k ∧ 2 * m ≤ n), erdosWeight n m := by
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro m hm
      by_cases hb : blockIndex n m = k
      · by_cases hh : 2 * m ≤ n <;> simp [hb, hh]
      · simp [hb]
    calc
      (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m)
          ≤ ∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
            if 2 * m ≤ n then erdosWeight n m else 0 := hsum_le_half
      _ = ∑ m ∈ (Finset.Icc 1 (n - 1)).filter
            (fun m => blockIndex n m = k ∧ 2 * m ≤ n), erdosWeight n m := hhalf_eq
      _ ≤ leftBlockMajorant k := by
            simpa [leftBlockMajorant] using kernel_block_left_half_le n k hn
      _ = (if K ≤ k then leftBlockMajorant k else 0) := by simp [hKk]
  · have hzero :
        ∀ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m = 0 := by
      intro m hm
      by_cases htail : (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ)
      · have hge := tail_block_index_ge (n := n) (K := K) (k := k) (m := m) hn hm htail
        exact False.elim (hKk hge)
      · simp [f, htail]
    calc
      (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m)
          = 0 := Finset.sum_eq_zero hzero
      _ ≤ (if K ≤ k then leftBlockMajorant k else 0) := by simp [hKk]

lemma finite_block_majorant_tail_le_shifted_tsum (N K : ℕ) :
    (∑ k ∈ Finset.range N, if K ≤ k then leftBlockMajorant k else 0) ≤
      ∑' j : ℕ, leftBlockMajorant (j + K) := by
  classical
  let s := (Finset.range N).filter (fun k => K ≤ k)
  have hsum_filter :
      (∑ k ∈ Finset.range N, if K ≤ k then leftBlockMajorant k else 0) =
        ∑ k ∈ s, leftBlockMajorant k := by
    simp [s, Finset.sum_filter]
  let imageS : Finset ℕ := s.image (fun k => k - K)
  have hinj : Set.InjOn (fun k : ℕ => k - K) (↑s : Set ℕ) := by
    intro a ha b hb hsub
    have hKa : K ≤ a := by
      have hmem : a ∈ s := by simpa using ha
      exact (Finset.mem_filter.mp hmem).2
    have hKb : K ≤ b := by
      have hmem : b ∈ s := by simpa using hb
      exact (Finset.mem_filter.mp hmem).2
    have hsub' : a - K = b - K := hsub
    calc
      a = (a - K) + K := (Nat.sub_add_cancel hKa).symm
      _ = (b - K) + K := by rw [hsub']
      _ = b := Nat.sub_add_cancel hKb
  have hreindex :
      (∑ k ∈ s, leftBlockMajorant k) =
        ∑ j ∈ imageS, leftBlockMajorant (j + K) := by
    dsimp [imageS]
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro k hk
      have hKk : K ≤ k := (Finset.mem_filter.mp hk).2
      congr 1
      omega
    · intro a ha b hb h
      exact hinj (by simpa using ha) (by simpa using hb) h
  have himage_subset : imageS ⊆ Finset.range N := by
    intro j hj
    dsimp [imageS] at hj
    rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
    have hkN : k < N := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    exact Finset.mem_range.mpr (by omega)
  have hfinite_le_range :
      (∑ j ∈ imageS, leftBlockMajorant (j + K)) ≤
        ∑ j ∈ Finset.range N, leftBlockMajorant (j + K) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
      (fun j _hj _hnot => leftBlockMajorant_nonneg (j + K))
  have hshift_summable : Summable fun j : ℕ => leftBlockMajorant (j + K) := by
    exact summable_leftBlockMajorant.comp_injective (fun a b h => by omega)
  have hprefix_le_tsum :
      (∑ j ∈ Finset.range N, leftBlockMajorant (j + K)) ≤
        ∑' j : ℕ, leftBlockMajorant (j + K) := by
    exact hshift_summable.sum_le_tsum (Finset.range N)
      (fun j _hj => leftBlockMajorant_nonneg (j + K))
  calc
    (∑ k ∈ Finset.range N, if K ≤ k then leftBlockMajorant k else 0)
        = ∑ k ∈ s, leftBlockMajorant k := hsum_filter
    _ = ∑ j ∈ imageS, leftBlockMajorant (j + K) := hreindex
    _ ≤ ∑ j ∈ Finset.range N, leftBlockMajorant (j + K) := hfinite_le_range
    _ ≤ ∑' j : ℕ, leftBlockMajorant (j + K) := hprefix_le_tsum

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos.Close
end

section
/-!
# Mass-rate campaign: the Lambert identity for `M₀` (R8 §2.1)

`M₀(t) = Σ_m σ(m)e^{−tm} = Σ_k boseKernel(tk)` — via Mathlib's
`tsum_prod_pow_eq_tsum_sigma` (divisors-antidiagonal Lambert machinery from the
Eisenstein q-expansion development) at `k = 1`, `r = e^{−t}`, with the
geometric-derivative inner sum `Σ'_{c:ℕ+} c·y^c = y/(1−y)²`.  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter Finset
open scoped BigOperators Topology ArithmeticFunction.sigma

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `σR` agrees with the arithmetic-function `σ 1` (cast). -/
lemma sigmaR_eq_sigma_one (m : ℕ) : Sigma.sigmaR m = ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) := rfl

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Mass-rate campaign: the `M₁` Lambert identity by termwise differentiation

`M₁(t) = Σ_k k·boseKernel2(tk)`, `boseKernel2(z) = e^{−z}(1+e^{−z})/(1−e^{−z})³ = Σ_d d²e^{−dz}`
— obtained by differentiating both sides of the banked `M₀` Lambert identity termwise on
`Ioi (t/2)` via `hasDerivAt_tsum_of_isPreconnected`, then `HasDerivAt.unique`.
Replaces the retired antidiagonal draft.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Summability of `m^j·σ(m)·r^m` for `‖r‖ < 1`. -/
lemma summable_pow_sigma_geometric (j : ℕ) {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun m : ℕ => (m : ℝ) ^ j * Sigma.sigmaR m * |r| ^ m) := by
  have hr' : ‖|r|‖ < 1 := by
    rw [Real.norm_eq_abs, abs_abs]
    rwa [Real.norm_eq_abs] at hr
  have hbig := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (j + 2) hr'
  refine Summable.of_nonneg_of_le
    (f := fun m : ℕ => ((m : ℝ)) ^ (j + 2) * |r| ^ m) (fun m => ?_) (fun m => ?_) hbig
  · have := sigmaR_nonneg m
    positivity
  ·
    by_cases hm : m = 0
    · subst hm
      have hσ0 : Sigma.sigmaR 0 = 0 := by
        rw [sigmaR_eq_sigma_one]
        simp
      simp only [hσ0, Nat.cast_zero, mul_zero, zero_mul]
      positivity
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hσ : Sigma.sigmaR m ≤ (m : ℝ) ^ 2 := sigmaR_le_square hm1
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have habs : (0 : ℝ) ≤ |r| ^ m := by positivity
      calc (m : ℝ) ^ j * Sigma.sigmaR m * |r| ^ m
          ≤ (m : ℝ) ^ j * (m : ℝ) ^ 2 * |r| ^ m := by
            apply mul_le_mul_of_nonneg_right _ habs
            exact mul_le_mul_of_nonneg_left hσ (by positivity)
        _ = (m : ℝ) ^ (j + 2) * |r| ^ m := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Mass-rate campaign: §5 the second-order divisor calc

`kernelMass n = ∑_{m=1}^{n-1} σ(m)/(n−m)·exp(−C(√n−√(n−m)))` versus
`kernelMassApprox2 n = (1/n)M₀(t)+(1/n²)M₁(t)−(C/(8n²√n))M₂(t)` at `t=λ/√n`.

Brick 1 here: `kernelMassApprox2 n = ∑' m, modelSummand n m`, where
`modelSummand n m = σ(m)·e^{−tm}·(1/n + m/n² − Cm²/(8n²√n))` — i.e. the moment package collapses
to a single divisor-weighted Lambert sum.  This is the object the per-term estimate
`erdosWeight_coef_second_order` (#97), multiplied by `σ(m)≥0`, is compared against.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

private lemma sigmaR_zero : Sigma.sigmaR 0 = 0 := by
  simp [Sigma.sigmaR]

/-- Summability of the (sign-adjusted) Lambert summand `m^r σ(m) e^{−tm}` for `t > 0`. -/
private lemma summable_sigma_exp (r : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ =>
      if m = 0 then (0:ℝ) else (m:ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m:ℝ))) := by
  have hnorm : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hg := summable_pow_sigma_geometric r (r := Real.exp (-t)) hnorm
  refine hg.congr ?_
  intro m
  rcases eq_or_ne m 0 with h | h
  · subst h; simp [sigmaR_zero]
  · rw [if_neg h, abs_of_pos (Real.exp_pos _)]
    have hpow : Real.exp (-t) ^ m = Real.exp (-t * (m:ℝ)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hpow]

/-- **Model identity** (§5 brick 1): `kernelMassApprox2 n = ∑' m, modelSummand n m`. -/
theorem kernelMassApprox2_eq_tsum_model {n : ℕ} (hn : 1 ≤ n) :
    kernelMassApprox2 n = ∑' m : ℕ, modelSummand n m := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have ht0 : 0 < massLam / Real.sqrt (n:ℝ) := div_pos massLam_pos hs0
  -- scaled summability of the three Lambert summands
  have h0c : Summable (fun m : ℕ => (1 / (n:ℝ)) *
      (if m = 0 then (0:ℝ) else (m:ℝ) ^ 0 * Sigma.sigmaR m *
        Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))) :=
    (summable_sigma_exp 0 ht0).mul_left _
  have h1c : Summable (fun m : ℕ => (1 / (n:ℝ) ^ 2) *
      (if m = 0 then (0:ℝ) else (m:ℝ) ^ 1 * Sigma.sigmaR m *
        Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))) :=
    (summable_sigma_exp 1 ht0).mul_left _
  have h2c : Summable (fun m : ℕ => (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) *
      (if m = 0 then (0:ℝ) else (m:ℝ) ^ 2 * Sigma.sigmaR m *
        Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))) :=
    (summable_sigma_exp 2 ht0).mul_left _
  simp only [kernelMassApprox2, sigmaMoment]
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  rw [← h0c.tsum_add h1c, ← (h0c.add h1c).tsum_sub h2c]
  apply tsum_congr
  intro m
  rcases eq_or_ne m 0 with h | h
  · subst h; simp [modelSummand]
  · simp only [if_neg h, modelSummand]
    ring

/-- **Error-moment bound** (§5 brick 2): the divisor-weighted majorant of the second-order error,
`(3C²+5C+2)·[(1/n³)M₂ + (1/(n³√n))M₃ + (1/n⁴)M₄]` at `t=λ/√n`, is `O(1/n)`.  Pure application of the
sharp moment bound `sigmaMoment_le_power_sharp` (#119) at `r=2,3,4` with `t=λ/√n` (so
`1/t^{r+2}=O(n^{(r+2)/2})`).  This is the `O(1/n)` core that the main-range `#97×σ(m)` error sums to. -/
theorem model_error_moment_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (3 * C ^ 2 + 5 * C + 2) *
        ((1 / (n:ℝ) ^ 3) * sigmaMoment 2 (massLam / Real.sqrt (n:ℝ))
         + (1 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
         + (1 / (n:ℝ) ^ 4) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ)))
        ≤ K / (n:ℝ) := by
  obtain ⟨K2, hK2nn, hK2⟩ := sigmaMoment_le_power_sharp 2
  obtain ⟨K3, hK3nn, hK3⟩ := sigmaMoment_le_power_sharp 3
  obtain ⟨K4, hK4nn, hK4⟩ := sigmaMoment_le_power_sharp 4
  set lam : ℝ := massLam with hlamdef
  have hlam0 : 0 < lam := massLam_pos
  have hlamne : lam ≠ 0 := hlam0.ne'
  have hCpos : 0 < C := C_pos
  have hcoef : 0 ≤ 3 * C ^ 2 + 5 * C + 2 := by positivity
  have hinner : 0 ≤ K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6 :=
    add_nonneg (add_nonneg (div_nonneg hK2nn (by positivity)) (div_nonneg hK3nn (by positivity)))
      (div_nonneg hK4nn (by positivity))
  refine ⟨(3 * C ^ 2 + 5 * C + 2) * (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) + 1, ?_, ?_⟩
  · have := mul_nonneg hcoef hinner; linarith
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (1:ℝ) ≤ (n : ℝ) ∧ lam ^ 2 ≤ (n : ℝ) := by
    rw [eventually_atTop]
    refine ⟨max 1 ⌈lam ^ 2⌉₊, fun n hn => ?_⟩
    refine ⟨by exact_mod_cast (le_trans (le_max_left _ _) hn), ?_⟩
    have h2 : (⌈lam ^ 2⌉₊ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_trans (le_max_right _ _) hn)
    exact le_trans (Nat.le_ceil _) h2
  filter_upwards [hev] with n hn
  obtain ⟨hn1, hnlam⟩ := hn
  have hnpos : (0:ℝ) < (n : ℝ) := by linarith
  set s : ℝ := Real.sqrt (n:ℝ) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hnpos
  have hsne : s ≠ 0 := hs0.ne'
  have hs2 : s ^ 2 = (n : ℝ) := by rw [hsdef, Real.sq_sqrt hnpos.le]
  set t : ℝ := lam / s with htdef
  have ht0 : 0 < t := by rw [htdef]; positivity
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one hs0, ← Real.sqrt_sq hlam0.le, hsdef]
    exact Real.sqrt_le_sqrt hnlam
  have hM2 := hK2 t ht0 ht1
  have hM3 := hK3 t ht0 ht1
  have hM4 := hK4 t ht0 ht1
  -- per-term bounds, each ≤ (Kr/lam^?)/n
  have e2 : (1 / (n:ℝ) ^ 3) * (K2 / t ^ 4) = (K2 / lam ^ 4) / (n:ℝ) := by
    rw [htdef, ← hs2]; field_simp
  have e3 : (1 / ((n:ℝ) ^ 3 * s)) * (K3 / t ^ 5) = (K3 / lam ^ 5) / (n:ℝ) := by
    rw [htdef, ← hs2]; field_simp
  have e4 : (1 / (n:ℝ) ^ 4) * (K4 / t ^ 6) = (K4 / lam ^ 6) / (n:ℝ) := by
    rw [htdef, ← hs2]; field_simp
  have b2 : (1 / (n:ℝ) ^ 3) * sigmaMoment 2 t ≤ (K2 / lam ^ 4) / (n:ℝ) := by
    rw [← e2]; exact mul_le_mul_of_nonneg_left hM2 (by positivity)
  have b3 : (1 / ((n:ℝ) ^ 3 * s)) * sigmaMoment 3 t ≤ (K3 / lam ^ 5) / (n:ℝ) := by
    rw [← e3]; exact mul_le_mul_of_nonneg_left hM3 (by positivity)
  have b4 : (1 / (n:ℝ) ^ 4) * sigmaMoment 4 t ≤ (K4 / lam ^ 6) / (n:ℝ) := by
    rw [← e4]; exact mul_le_mul_of_nonneg_left hM4 (by positivity)
  -- assemble; note the goal's sqrt/massLam fold to s/lam/t
  have hsum : (1 / (n:ℝ) ^ 3) * sigmaMoment 2 t
      + (1 / ((n:ℝ) ^ 3 * s)) * sigmaMoment 3 t
      + (1 / (n:ℝ) ^ 4) * sigmaMoment 4 t
      ≤ (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) / (n:ℝ) := by
    have : (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) / (n:ℝ)
        = (K2 / lam ^ 4) / (n:ℝ) + (K3 / lam ^ 5) / (n:ℝ) + (K4 / lam ^ 6) / (n:ℝ) := by ring
    rw [this]; linarith [b2, b3, b4]
  calc (3 * C ^ 2 + 5 * C + 2) *
        ((1 / (n:ℝ) ^ 3) * sigmaMoment 2 t
         + (1 / ((n:ℝ) ^ 3 * s)) * sigmaMoment 3 t
         + (1 / (n:ℝ) ^ 4) * sigmaMoment 4 t)
      ≤ (3 * C ^ 2 + 5 * C + 2) *
          ((K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) / (n:ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hcoef
    _ ≤ ((3 * C ^ 2 + 5 * C + 2) * (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) + 1) / (n:ℝ) := by
        have h1n : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
        have hL : (3 * C ^ 2 + 5 * C + 2) * ((K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) / (n:ℝ))
            = (3 * C ^ 2 + 5 * C + 2) * (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) / (n:ℝ) := by
          ring
        have hR : ((3 * C ^ 2 + 5 * C + 2) * (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) + 1) / (n:ℝ)
            = (3 * C ^ 2 + 5 * C + 2) * (K2 / lam ^ 4 + K3 / lam ^ 5 + K4 / lam ^ 6) / (n:ℝ)
              + 1 / (n:ℝ) := by ring
        rw [hL, hR]; linarith

/-- The main cutoff `⌊n^{2/3}⌋`: for `n` large, every `1 ≤ m ≤ ⌊n^{2/3}⌋` satisfies the two
side-conditions of `erdosWeight_coef_second_order` (#97): `2m ≤ n` and `4Cm² ≤ √n³`. -/
private lemma mainCut_cond :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℕ, 1 ≤ m → m ≤ ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ →
      2 * m ≤ n ∧ 4 * C * (m:ℝ) ^ 2 ≤ Real.sqrt (n:ℝ) ^ 3 := by
  have hCpos : 0 < C := C_pos
  rw [Filter.eventually_atTop]
  refine ⟨max 8 (⌈(4 * C) ^ 6⌉₊ + 1), fun n hn m hm1 hmle => ?_⟩
  have hn8 : 8 ≤ n := le_trans (le_max_left _ _) hn
  have hnC : ⌈(4 * C) ^ 6⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hp23 : (0:ℝ) ≤ (n:ℝ) ^ (2/3 : ℝ) := Real.rpow_nonneg hnpos.le _
  -- (m:ℝ) ≤ n^{2/3}
  have hmr : (m:ℝ) ≤ (n:ℝ) ^ (2/3 : ℝ) :=
    le_trans (by exact_mod_cast hmle) (Nat.floor_le hp23)
  have hmr0 : (0:ℝ) ≤ (m:ℝ) := by positivity
  -- cube root: 2 ≤ n^{1/3}
  have hcubrt : (2:ℝ) ≤ (n:ℝ) ^ (1/3 : ℝ) := by
    have h8 : (8:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn8
    have hmono : (8:ℝ) ^ (1/3 : ℝ) ≤ (n:ℝ) ^ (1/3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h8 (by norm_num)
    have h83 : (8:ℝ) ^ (1/3 : ℝ) = 2 := by
      rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, ← Real.rpow_natCast 2 3,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    rwa [h83] at hmono
  -- sixth root: 4C ≤ n^{1/6}
  have hsixrt : 4 * C ≤ (n:ℝ) ^ (1/6 : ℝ) := by
    have hbase : ((4 * C) ^ 6 : ℝ) ≤ (n:ℝ) := by
      have h1 : ((4 * C) ^ 6 : ℝ) ≤ (⌈(4 * C) ^ 6⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈(4 * C) ^ 6⌉₊ : ℕ):ℝ) ≤ (n:ℝ) := by
        have : ⌈(4 * C) ^ 6⌉₊ ≤ n := by omega
        exact_mod_cast this
      linarith
    have hmono : ((4 * C) ^ 6 : ℝ) ^ (1/6 : ℝ) ≤ (n:ℝ) ^ (1/6 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hbase (by norm_num)
    have hid : ((4 * C) ^ 6 : ℝ) ^ (1/6 : ℝ) = 4 * C := by
      rw [← Real.rpow_natCast (4 * C) 6, ← Real.rpow_mul (by positivity)]
      have h6 : ((6 : ℕ) : ℝ) * (1 / 6 : ℝ) = 1 := by norm_num
      rw [h6, Real.rpow_one]
    rwa [hid] at hmono
  -- power identities
  have hn1 : (n:ℝ) = (n:ℝ) ^ (1/3 : ℝ) * (n:ℝ) ^ (2/3 : ℝ) := by
    rw [← Real.rpow_add hnpos, show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num, Real.rpow_one]
  have hsqrtcube : Real.sqrt (n:ℝ) ^ 3 = ((n:ℝ) ^ (2/3 : ℝ)) ^ 2 * (n:ℝ) ^ (1/6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((n:ℝ) ^ (1/2 : ℝ)) 3,
      ← Real.rpow_mul hnpos.le, ← Real.rpow_natCast ((n:ℝ) ^ (2/3 : ℝ)) 2,
      ← Real.rpow_mul hnpos.le, ← Real.rpow_add hnpos]
    norm_num
  refine ⟨?_, ?_⟩
  · -- 2 m ≤ n
    have hreal : 2 * (m:ℝ) ≤ (n:ℝ) := by
      calc 2 * (m:ℝ) ≤ 2 * (n:ℝ) ^ (2/3 : ℝ) := by linarith
        _ ≤ (n:ℝ) ^ (1/3 : ℝ) * (n:ℝ) ^ (2/3 : ℝ) := by
            apply mul_le_mul_of_nonneg_right hcubrt hp23
        _ = (n:ℝ) := hn1.symm
    exact_mod_cast hreal
  · -- 4 C m² ≤ √n³
    have hm2 : (m:ℝ) ^ 2 ≤ ((n:ℝ) ^ (2/3 : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ hmr0 hmr 2
    calc 4 * C * (m:ℝ) ^ 2 ≤ 4 * C * ((n:ℝ) ^ (2/3 : ℝ)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hm2 (by positivity)
      _ ≤ (n:ℝ) ^ (1/6 : ℝ) * ((n:ℝ) ^ (2/3 : ℝ)) ^ 2 := by
          apply mul_le_mul_of_nonneg_right hsixrt (by positivity)
      _ = Real.sqrt (n:ℝ) ^ 3 := by rw [hsqrtcube]; ring

/-- **Main-range error sum** (§5 brick 4): `∑_{m=1}^{⌊n^{2/3}⌋} |erdosWeight − modelSummand| ≤ K/n`.
Per-term `#97×σ(m)` (brick 3) on the cutoff range, then the finite divisor sums are `≤` the full
Lambert moments (`sum_le_tsum`), reducing to the `O(1/n)` moment bound (brick 2). -/
theorem main_range_error_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (∑ m ∈ Finset.Icc 1 ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊, |erdosWeight n m - modelSummand n m|)
        ≤ K / (n:ℝ) := by
  obtain ⟨K, hKpos, hKbound⟩ := model_error_moment_bound
  have hCpos : 0 < C := C_pos
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [mainCut_cond, hKbound, Filter.eventually_ge_atTop 1] with n hcond hKb hn1
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have ht0 : 0 < massLam / Real.sqrt (n:ℝ) := div_pos massLam_pos hs0
  set M : ℕ := ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ with hM
  -- step 1: per-term #97×σ
  have hstep1 : (∑ m ∈ Finset.Icc 1 M, |erdosWeight n m - modelSummand n m|)
      ≤ ∑ m ∈ Finset.Icc 1 M, Sigma.sigmaR m * ((3 * C ^ 2 + 5 * C + 2) *
          Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
          ((m:ℝ) ^ 2 / (n:ℝ) ^ 3 + (m:ℝ) ^ 3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))
            + (m:ℝ) ^ 4 / (n:ℝ) ^ 4)) := by
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨hm1, hmle⟩ := hm
    obtain ⟨h2m, hsmall⟩ := hcond m hm1 hmle
    exact erdosWeight_sub_model_le hn1 hm1 h2m hsmall
  -- step 2: rearrange each summand into the three moment summands
  have hrw : ∀ m : ℕ, Sigma.sigmaR m * ((3 * C ^ 2 + 5 * C + 2) *
        Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)) *
        ((m:ℝ) ^ 2 / (n:ℝ) ^ 3 + (m:ℝ) ^ 3 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))
          + (m:ℝ) ^ 4 / (n:ℝ) ^ 4))
      = (3 * C ^ 2 + 5 * C + 2) *
          ((1 / (n:ℝ) ^ 3) * ((m:ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
           + (1 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * ((m:ℝ) ^ 3 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
           + (1 / (n:ℝ) ^ 4) * ((m:ℝ) ^ 4 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))) := by
    intro m; ring
  rw [Finset.sum_congr rfl (fun m _ => hrw m), ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hstep1
  -- step 3: each finite divisor sum ≤ the full Lambert moment
  have hfin : ∀ r : ℕ, (∑ m ∈ Finset.Icc 1 M,
        (m:ℝ) ^ r * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
      ≤ sigmaMoment r (massLam / Real.sqrt (n:ℝ)) := by
    intro r
    have hge0 : ∀ k : ℕ, 0 ≤ (if k = 0 then (0:ℝ)
        else (k:ℝ) ^ r * Sigma.sigmaR k * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (k:ℝ))) := by
      intro k; rcases eq_or_ne k 0 with h | h
      · simp [h]
      · rw [if_neg h]
        exact mul_nonneg (mul_nonneg (by positivity) (sigmaR_nonneg k)) (Real.exp_pos _).le
    have hsumm := summable_sigma_exp r ht0
    have hle := sum_le_hasSum (Finset.Icc 1 M) (fun k _ => hge0 k) hsumm.hasSum
    rw [sigmaMoment]
    refine le_trans (le_of_eq ?_) hle
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [if_neg (by omega : ¬ m = 0)]
  -- combine
  have hmono : (3 * C ^ 2 + 5 * C + 2) *
        ((1 / (n:ℝ) ^ 3) * (∑ m ∈ Finset.Icc 1 M, (m:ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
         + (1 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * (∑ m ∈ Finset.Icc 1 M, (m:ℝ) ^ 3 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ)))
         + (1 / (n:ℝ) ^ 4) * (∑ m ∈ Finset.Icc 1 M, (m:ℝ) ^ 4 * Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))))
      ≤ (3 * C ^ 2 + 5 * C + 2) *
        ((1 / (n:ℝ) ^ 3) * sigmaMoment 2 (massLam / Real.sqrt (n:ℝ))
         + (1 / ((n:ℝ) ^ 3 * Real.sqrt (n:ℝ))) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
         + (1 / (n:ℝ) ^ 4) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ))) := by
    have hcoef : 0 ≤ 3 * C ^ 2 + 5 * C + 2 := by positivity
    apply mul_le_mul_of_nonneg_left _ hcoef
    gcongr <;> [exact hfin 2; exact hfin 3; exact hfin 4]
  exact le_trans hstep1 (le_trans hmono hKb)

/-- Exp beats poly with a sixth-root exponent: `(n:ℝ)^d · exp(−a·n^{1/6}) ≤ 1/n` eventually. The
analytic engine for both the far-`erdosWeight` tail and the `modelSummand` tail (cutoff `⌊n^{2/3}⌋`,
`t·⌊n^{2/3}⌋ ≍ n^{1/6}`). -/
lemma poly_mul_exp_neg_sixthRoot_le_inv (a : ℝ) (ha : 0 < a) (d : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n:ℝ) ^ d * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)) ≤ 1 / (n:ℝ) := by
  have htend : Filter.Tendsto
      (fun n : ℕ => (n:ℝ) ^ (d + 1) * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)))
      Filter.atTop (nhds 0) := by
    have hreal : Filter.Tendsto
        (fun x : ℝ => x ^ ((6 * (d + 1) : ℕ) : ℝ) * Real.exp (-a * x))
        Filter.atTop (nhds 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ a ha
    have hroot : Filter.Tendsto (fun n : ℕ => (n:ℝ) ^ (1/6 : ℝ)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    refine (hreal.comp hroot).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hpow : ((n:ℝ) ^ (1/6 : ℝ)) ^ ((6 * (d + 1) : ℕ) : ℝ) = (n:ℝ) ^ (d + 1) := by
      rw [← Real.rpow_mul hn0,
        show (1/6 : ℝ) * ((6 * (d + 1) : ℕ) : ℝ) = ((d + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    simp only [Function.comp]
    rw [hpow]
  have h1 : ∀ᶠ n : ℕ in Filter.atTop,
      (n:ℝ) ^ (d + 1) * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)) ≤ 1 :=
    htend.eventually_le_const (by norm_num)
  filter_upwards [h1, Filter.eventually_ge_atTop 1] with n hn1 hn
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hnpos]
  have hrw : (n:ℝ) ^ d * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)) * (n:ℝ)
      = (n:ℝ) ^ (d + 1) * Real.exp (-a * (n:ℝ) ^ (1/6 : ℝ)) := by ring
  rw [hrw]; exact hn1

/-- Exp beats poly with a √n exponent: `(n:ℝ)^d · exp(−a·√n) ≤ 1/n` eventually. Engine for the
right-half `erdosWeight` tail (`right_half_kernel_sum_le` gives `n³·exp(−(C/10)√n)`). -/
lemma poly_mul_exp_neg_sqrt_le_inv (a : ℝ) (ha : 0 < a) (d : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n:ℝ) ^ d * Real.exp (-a * Real.sqrt (n:ℝ)) ≤ 1 / (n:ℝ) := by
  have htend : Filter.Tendsto
      (fun n : ℕ => (n:ℝ) ^ (d + 1) * Real.exp (-a * Real.sqrt (n:ℝ)))
      Filter.atTop (nhds 0) := by
    have hreal : Filter.Tendsto
        (fun x : ℝ => x ^ ((2 * (d + 1) : ℕ) : ℝ) * Real.exp (-a * x))
        Filter.atTop (nhds 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ a ha
    have hroot : Filter.Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    refine (hreal.comp hroot).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hpow : (Real.sqrt (n:ℝ)) ^ ((2 * (d + 1) : ℕ) : ℝ) = (n:ℝ) ^ (d + 1) := by
      rw [Real.rpow_natCast]
      calc (Real.sqrt (n:ℝ)) ^ (2 * (d + 1))
          = ((Real.sqrt (n:ℝ)) ^ 2) ^ (d + 1) := by rw [← pow_mul]
        _ = (n:ℝ) ^ (d + 1) := by rw [Real.sq_sqrt hn0]
    simp only [Function.comp]
    rw [hpow]
  have h1 : ∀ᶠ n : ℕ in Filter.atTop,
      (n:ℝ) ^ (d + 1) * Real.exp (-a * Real.sqrt (n:ℝ)) ≤ 1 :=
    htend.eventually_le_const (by norm_num)
  filter_upwards [h1, Filter.eventually_ge_atTop 1] with n hn1 hn
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hnpos]
  have hrw : (n:ℝ) ^ d * Real.exp (-a * Real.sqrt (n:ℝ)) * (n:ℝ)
      = (n:ℝ) ^ (d + 1) * Real.exp (-a * Real.sqrt (n:ℝ)) := by ring
  rw [hrw]; exact hn1

/-- Geometric-quadratic tail of the left block majorants: shifting by `K` factors out `exp(−(C/2)K)`
and a `(K+1)²`, leaving a convergent constant `G = ∑'_j (j+1)²·exp(−C/2)^j`. -/
lemma leftBlockMajorant_shifted_tsum_le (K : ℕ) :
    (∑' j : ℕ, leftBlockMajorant (j + K))
      ≤ 2 * sigmaQuadConst * ((K:ℝ) + 1) ^ 2
          * (∑' j : ℕ, ((j:ℝ) + 1) ^ 2 * Real.exp (-(C / 2)) ^ j)
          * Real.exp (-(C / 2) * (K:ℝ)) := by
  have hCpos := C_pos
  have hsQ : 0 ≤ sigmaQuadConst := sigmaQuadConst_pos.le
  have hr : ‖Real.exp (-(C / 2))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hGsumm : Summable (fun j : ℕ => ((j:ℝ) + 1) ^ 2 * Real.exp (-(C / 2)) ^ j) := by
    have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
    have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hr
    refine ((h2.add (h1.mul_left 2)).add h0).congr (fun j => ?_)
    ring
  have hLsumm : Summable (fun j : ℕ => leftBlockMajorant (j + K)) :=
    summable_leftBlockMajorant.comp_injective (add_left_injective K)
  have hRsumm : Summable (fun j : ℕ => (2 * sigmaQuadConst * ((K:ℝ) + 1) ^ 2 *
      Real.exp (-(C / 2) * (K:ℝ))) * (((j:ℝ) + 1) ^ 2 * Real.exp (-(C / 2)) ^ j)) :=
    hGsumm.mul_left _
  have hbound : ∀ j : ℕ, leftBlockMajorant (j + K)
      ≤ (2 * sigmaQuadConst * ((K:ℝ) + 1) ^ 2 * Real.exp (-(C / 2) * (K:ℝ))) *
          (((j:ℝ) + 1) ^ 2 * Real.exp (-(C / 2)) ^ j) := by
    intro j
    rw [leftBlockMajorant]
    have hexp : Real.exp (-(C / 2) * ((j + K : ℕ) : ℝ))
        = Real.exp (-(C / 2) * (K:ℝ)) * Real.exp (-(C / 2)) ^ j := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    rw [hexp]
    have hle : (((j + K : ℕ) + 1 : ℕ) : ℝ) ≤ ((K:ℝ) + 1) * ((j:ℝ) + 1) := by
      push_cast
      nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ (j:ℝ)), (Nat.cast_nonneg K : (0:ℝ) ≤ (K:ℝ))]
    have hsq : (((j + K : ℕ) + 1 : ℕ) : ℝ) ^ 2 ≤ ((K:ℝ) + 1) ^ 2 * ((j:ℝ) + 1) ^ 2 := by
      have h0 : (0:ℝ) ≤ (((j + K : ℕ) + 1 : ℕ) : ℝ) := by positivity
      nlinarith [hle, h0]
    have hfac : (0:ℝ) ≤ Real.exp (-(C / 2) * (K:ℝ)) * Real.exp (-(C / 2)) ^ j := by positivity
    nlinarith [hsq, hsQ, hfac, mul_nonneg hsQ hfac,
      mul_nonneg (mul_nonneg hsQ hfac) (sq_nonneg ((j:ℝ) + 1))]
  calc (∑' j : ℕ, leftBlockMajorant (j + K))
      ≤ ∑' j : ℕ, (2 * sigmaQuadConst * ((K:ℝ) + 1) ^ 2 * Real.exp (-(C / 2) * (K:ℝ))) *
          (((j:ℝ) + 1) ^ 2 * Real.exp (-(C / 2)) ^ j) :=
        Summable.tsum_le_tsum hbound hLsumm hRsumm
    _ = 2 * sigmaQuadConst * ((K:ℝ) + 1) ^ 2 *
          (∑' j : ℕ, ((j:ℝ) + 1) ^ 2 * Real.exp (-(C / 2)) ^ j) * Real.exp (-(C / 2) * (K:ℝ)) := by
        rw [tsum_mul_left]; ring

/-- `modelSummand n` is summable (it is the divisor-weighted Lambert combination). -/
private lemma summable_modelSummand {n : ℕ} (hn : 1 ≤ n) : Summable (modelSummand n) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have ht0 : 0 < massLam / Real.sqrt (n:ℝ) := div_pos massLam_pos (Real.sqrt_pos.mpr hnpos)
  have hsum := (((summable_sigma_exp 0 ht0).mul_left (1 / (n:ℝ))).add
      ((summable_sigma_exp 1 ht0).mul_left (1 / (n:ℝ) ^ 2))).sub
      ((summable_sigma_exp 2 ht0).mul_left (C / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))))
  refine hsum.congr (fun m => ?_)
  rcases eq_or_ne m 0 with h | h
  · subst h; simp [modelSummand]
  · simp only [modelSummand, if_neg h]; ring

/-- **Far-`erdosWeight` tail** (§5 brick 6): `∑_{m=⌊n^{2/3}⌋+1}^{n-1} erdosWeight n m ≤ K/n`. Split
at `n<2m` (right half, `right_half_kernel_sum_le` + √n exp-beats-poly) vs `2m≤n` (left far, block
majorants at index `Kn=⌊n^{1/6}⌋` + geometric tail + sixth-root exp-beats-poly). -/
theorem far_erdos_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      (∑ m ∈ Finset.Icc (⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ + 1) (n - 1), erdosWeight n m) ≤ K / (n:ℝ) := by
  have hCpos := C_pos
  have hsQ : 0 ≤ sigmaQuadConst := sigmaQuadConst_pos.le
  set G : ℝ := ∑' j : ℕ, ((j:ℝ) + 1) ^ 2 * Real.exp (-(C / 2)) ^ j with hGdef
  have hGnn : 0 ≤ G := by rw [hGdef]; exact tsum_nonneg (fun j => by positivity)
  have hKLnn : 0 ≤ 8 * sigmaQuadConst * G * Real.exp (C / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsQ) hGnn) (Real.exp_pos _).le
  refine ⟨1 + 8 * sigmaQuadConst * G * Real.exp (C / 2) + 1, by linarith, ?_⟩
  filter_upwards [poly_mul_exp_neg_sqrt_le_inv (C / 10) (by linarith) 3,
    poly_mul_exp_neg_sixthRoot_le_inv (C / 2) (by linarith) 2,
    Filter.eventually_ge_atTop 2] with n hsqrt hsixth hn2
  have hn1 : 1 ≤ n := by omega
  have hn0' : 0 < n := by omega
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hnge1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have hew_nn : ∀ m, 0 ≤ erdosWeight n m := fun m => by
    rw [erdosWeight]
    exact mul_nonneg (div_nonneg (sigmaR_nonneg m) (by positivity)) (Real.exp_pos _).le
  set M : ℕ := ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ with hMdef
  set Kn : ℕ := ⌊(n:ℝ) ^ (1/6 : ℝ)⌋₊ with hKndef
  -- split each term: erdosWeight = right-indicator + left-indicator
  have hsplit : ∀ m : ℕ, erdosWeight n m
      = (if n < 2 * m then erdosWeight n m else 0) + (if 2 * m ≤ n then erdosWeight n m else 0) := by
    intro m; rcases lt_or_ge n (2 * m) with h | h
    · rw [if_pos h, if_neg (by omega)]; ring
    · rw [if_neg (by omega), if_pos h]; ring
  rw [Finset.sum_congr rfl (fun m _ => hsplit m), Finset.sum_add_distrib]
  -- right half ≤ 1/n
  have hright : (∑ m ∈ Finset.Icc (M + 1) (n - 1), if n < 2 * m then erdosWeight n m else 0)
      ≤ 1 / (n:ℝ) := by
    have h1 : (∑ m ∈ Finset.Icc (M + 1) (n - 1), if n < 2 * m then erdosWeight n m else 0)
        ≤ (n:ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (n:ℝ)) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc (by omega) le_rfl) (fun m _ _ => ?_)) (right_half_kernel_sum_le n)
      split
      · exact hew_nn m
      · exact le_rfl
    linarith [h1, hsqrt]
  -- left far ≤ 8 sQ G exp(C/2) / n
  have hKn_le : (Kn:ℝ) ≤ (n:ℝ) ^ (1/6 : ℝ) := Nat.floor_le (by positivity)
  have h16le : (n:ℝ) ^ (1/6 : ℝ) ≤ (n:ℝ) := by
    calc (n:ℝ) ^ (1/6 : ℝ) ≤ (n:ℝ) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnge1 (by norm_num)
      _ = (n:ℝ) := Real.rpow_one _
  have hKnge : (n:ℝ) ^ (1/6 : ℝ) - 1 ≤ (Kn:ℝ) := by
    have := Nat.lt_floor_add_one ((n:ℝ) ^ (1/6 : ℝ)); rw [← hKndef] at this; linarith
  have hleft : (∑ m ∈ Finset.Icc (M + 1) (n - 1), if 2 * m ≤ n then erdosWeight n m else 0)
      ≤ 8 * sigmaQuadConst * G * Real.exp (C / 2) * (1 / (n:ℝ)) := by
    -- relate to the Kn√n ∧ 2m≤n condition
    have hcond : (∑ m ∈ Finset.Icc (M + 1) (n - 1), if 2 * m ≤ n then erdosWeight n m else 0)
        ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
            if (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (m:ℝ) ∧ 2 * m ≤ n then erdosWeight n m else 0 := by
      calc (∑ m ∈ Finset.Icc (M + 1) (n - 1), if 2 * m ≤ n then erdosWeight n m else 0)
          ≤ ∑ m ∈ Finset.Icc (M + 1) (n - 1),
              if (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (m:ℝ) ∧ 2 * m ≤ n then erdosWeight n m else 0 := by
            apply Finset.sum_le_sum; intro m hm
            rw [Finset.mem_Icc] at hm
            have hKnm : (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (m:ℝ) := by
              have hm_gt : (n:ℝ) ^ (2/3 : ℝ) < (m:ℝ) := by
                have hlt : (n:ℝ) ^ (2/3 : ℝ) < (M:ℝ) + 1 := by
                  have := Nat.lt_floor_add_one ((n:ℝ) ^ (2/3 : ℝ)); rw [← hMdef] at this; linarith
                have hge : (M:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hm.1
                linarith
              calc (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (n:ℝ) ^ (1/6 : ℝ) * Real.sqrt (n:ℝ) :=
                    mul_le_mul_of_nonneg_right hKn_le (Real.sqrt_nonneg _)
                _ = (n:ℝ) ^ (2/3 : ℝ) := by
                    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]; norm_num
                _ ≤ (m:ℝ) := le_of_lt hm_gt
            by_cases h2 : 2 * m ≤ n
            · rw [if_pos h2, if_pos ⟨hKnm, h2⟩]
            · rw [if_neg h2, if_neg (fun h => h2 h.2)]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Icc_subset_Icc (by omega) le_rfl) (fun m _ _ => by split_ifs with h; exacts [hew_nn m, le_refl 0])
    have hchain : (∑ m ∈ Finset.Icc 1 (n - 1),
        if (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (m:ℝ) ∧ 2 * m ≤ n then erdosWeight n m else 0)
        ≤ 2 * sigmaQuadConst * ((Kn:ℝ) + 1) ^ 2 * G * Real.exp (-(C / 2) * (Kn:ℝ)) := by
      calc _ ≤ ∑ k ∈ Finset.range (numBlocks n),
              if Kn ≤ k then leftBlockMajorant k else 0 :=
            left_half_tail_sum_le_block_majorants n Kn hn0'
        _ ≤ ∑' j : ℕ, leftBlockMajorant (j + Kn) :=
            finite_block_majorant_tail_le_shifted_tsum _ _
        _ ≤ _ := leftBlockMajorant_shifted_tsum_le Kn
    -- (Kn+1)² exp(−(C/2)Kn) ≤ 4 exp(C/2) / n
    have hKbound : ((Kn:ℝ) + 1) ^ 2 * Real.exp (-(C / 2) * (Kn:ℝ)) ≤ 4 * Real.exp (C / 2) * (1 / (n:ℝ)) := by
      have hexpKn : Real.exp (-(C / 2) * (Kn:ℝ))
          ≤ Real.exp (C / 2) * Real.exp (-(C / 2) * (n:ℝ) ^ (1/6 : ℝ)) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [hKnge, hCpos]
      have hsqle : ((Kn:ℝ) + 1) ^ 2 ≤ 4 * (n:ℝ) ^ 2 := by
        have : (Kn:ℝ) + 1 ≤ 2 * (n:ℝ) := by
          have := hKn_le; have := h16le; have : (1:ℝ) ≤ (n:ℝ) := hnge1; nlinarith
        nlinarith [this, (Nat.cast_nonneg Kn : (0:ℝ) ≤ (Kn:ℝ))]
      calc ((Kn:ℝ) + 1) ^ 2 * Real.exp (-(C / 2) * (Kn:ℝ))
          ≤ (4 * (n:ℝ) ^ 2) * (Real.exp (C / 2) * Real.exp (-(C / 2) * (n:ℝ) ^ (1/6 : ℝ))) :=
            mul_le_mul hsqle hexpKn (Real.exp_pos _).le (by positivity)
        _ = 4 * Real.exp (C / 2) * ((n:ℝ) ^ 2 * Real.exp (-(C / 2) * (n:ℝ) ^ (1/6 : ℝ))) := by ring
        _ ≤ 4 * Real.exp (C / 2) * (1 / (n:ℝ)) :=
            mul_le_mul_of_nonneg_left hsixth (by positivity)
    calc (∑ m ∈ Finset.Icc (M + 1) (n - 1), if 2 * m ≤ n then erdosWeight n m else 0)
        ≤ 2 * sigmaQuadConst * ((Kn:ℝ) + 1) ^ 2 * G * Real.exp (-(C / 2) * (Kn:ℝ)) :=
          le_trans hcond hchain
      _ = 2 * sigmaQuadConst * G * (((Kn:ℝ) + 1) ^ 2 * Real.exp (-(C / 2) * (Kn:ℝ))) := by ring
      _ ≤ 2 * sigmaQuadConst * G * (4 * Real.exp (C / 2) * (1 / (n:ℝ))) :=
          mul_le_mul_of_nonneg_left hKbound (by positivity)
      _ = 8 * sigmaQuadConst * G * Real.exp (C / 2) * (1 / (n:ℝ)) := by ring
  have hfinal : 1 / (n:ℝ) + 8 * sigmaQuadConst * G * Real.exp (C / 2) * (1 / (n:ℝ))
      ≤ (1 + 8 * sigmaQuadConst * G * Real.exp (C / 2) + 1) / (n:ℝ) := by
    rw [add_div, add_div]; have : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
    have h8 : 8 * sigmaQuadConst * G * Real.exp (C / 2) * (1 / (n:ℝ))
        = (8 * sigmaQuadConst * G * Real.exp (C / 2)) / (n:ℝ) := by ring
    rw [h8]; linarith
  linarith [hright, hleft, hfinal]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 1000000
open Filter
open scoped Topology BigOperators
open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close
theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      |kernelMass n - kernelMassApprox2 n| ≤ K / (n:ℝ) := by
  obtain ⟨KA, hKApos, hKA⟩ := main_range_error_le
  obtain ⟨KB, hKBpos, hKB⟩ := far_erdos_tail_le
  obtain ⟨KC, hKCpos, hKC⟩ := model_tail_le
  refine ⟨KA + KB + KC, by linarith, ?_⟩
  filter_upwards [hKA, hKB, hKC, Filter.eventually_ge_atTop 2] with n hkA hkB hkC hn2
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hew_nn : ∀ m, 0 ≤ erdosWeight n m := fun m => by
    rw [erdosWeight]
    exact mul_nonneg (div_nonneg (sigmaR_nonneg m) (by positivity)) (Real.exp_pos _).le
  set M : ℕ := ⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ with hMdef
  -- M < n hence M ≤ n - 1
  have hMlt : M < n := by
    have h1 : (M:ℝ) ≤ (n:ℝ) ^ (2/3 : ℝ) := Nat.floor_le (by positivity)
    have h2 : (n:ℝ) ^ (2/3 : ℝ) < (n:ℝ) := by
      calc (n:ℝ) ^ (2/3 : ℝ) < (n:ℝ) ^ (1:ℝ) :=
            Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hn2) (by norm_num)
        _ = (n:ℝ) := Real.rpow_one _
    have : (M:ℝ) < (n:ℝ) := by linarith
    exact_mod_cast this
  have hMn1 : M ≤ n - 1 := by omega
  -- split kernelMass
  have hKsplit : kernelMass n = (∑ m ∈ Finset.Icc 1 M, erdosWeight n m)
      + (∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m) := by
    have e1 : Finset.Icc 1 M = Finset.Ioc 0 M := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have e2 : Finset.Icc (M + 1) (n - 1) = Finset.Ioc M (n - 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have e3 : Finset.Icc 1 (n - 1) = Finset.Ioc 0 (n - 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [kernelMass, e1, e2, e3, Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMn1]
  -- split kernelMassApprox2 = head + tail
  have hsumm := summable_modelSummand hn1
  have hheadsumm : Summable (fun m : ℕ => if m ≤ M then modelSummand n m else 0) :=
    summable_of_ne_finset_zero (s := Finset.range (M + 1)) (fun b hb => by
      rw [Finset.mem_range] at hb; rw [if_neg (by omega)])
  have htailsumm : Summable (fun m : ℕ => if m ≤ M then (0:ℝ) else modelSummand n m) := by
    refine (hsumm.sub hheadsumm).congr (fun m => ?_); split <;> simp
  have hhead : (∑' m : ℕ, if m ≤ M then modelSummand n m else 0)
      = ∑ m ∈ Finset.Icc 1 M, modelSummand n m := by
    rw [tsum_eq_sum (s := Finset.Icc 0 M)
      (fun b hb => by rw [Finset.mem_Icc] at hb; rw [if_neg (by omega)])]
    rw [show Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp [Finset.mem_Icc]), if_pos (Nat.zero_le M)]
    have h0 : modelSummand n 0 = 0 := by simp [modelSummand]
    rw [h0, zero_add]
    exact Finset.sum_congr rfl (fun m hm => if_pos (Finset.mem_Icc.mp hm).2)
  have hAsplit : kernelMassApprox2 n = (∑ m ∈ Finset.Icc 1 M, modelSummand n m)
      + (∑' m : ℕ, if m ≤ M then (0:ℝ) else modelSummand n m) := by
    rw [kernelMassApprox2_eq_tsum_model hn1, ← hhead, ← hheadsumm.tsum_add htailsumm]
    exact tsum_congr (fun m => by split <;> simp)
  -- assemble
  set tail : ℝ := ∑' m : ℕ, if m ≤ M then (0:ℝ) else modelSummand n m with htaildef
  rw [hKsplit, hAsplit]
  have hrw : (∑ m ∈ Finset.Icc 1 M, erdosWeight n m)
        + (∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m)
        - ((∑ m ∈ Finset.Icc 1 M, modelSummand n m) + tail)
      = (∑ m ∈ Finset.Icc 1 M, (erdosWeight n m - modelSummand n m))
        + (∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m) - tail := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hrw]
  have hBnn : 0 ≤ ∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m :=
    Finset.sum_nonneg (fun m _ => hew_nn m)
  have hAbsA : |∑ m ∈ Finset.Icc 1 M, (erdosWeight n m - modelSummand n m)|
      ≤ KA / (n:ℝ) := le_trans (Finset.abs_sum_le_sum_abs _ _) hkA
  have hAbsTail : |tail| ≤ KC / (n:ℝ) := by
    rw [htaildef]
    refine le_trans (le_trans (le_of_eq (Real.norm_eq_abs _).symm) ?_) hkC
    refine le_trans (norm_tsum_le_tsum_norm ?_) (le_of_eq ?_)
    · refine htailsumm.abs.congr (fun m => ?_); split <;> simp
    · refine tsum_congr (fun m => ?_); split <;> simp
  calc |(∑ m ∈ Finset.Icc 1 M, (erdosWeight n m - modelSummand n m))
          + (∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m) - tail|
      ≤ |(∑ m ∈ Finset.Icc 1 M, (erdosWeight n m - modelSummand n m))
          + (∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m)| + |tail| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ (|∑ m ∈ Finset.Icc 1 M, (erdosWeight n m - modelSummand n m)|
          + |∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m|) + |tail| := by
        gcongr; exact abs_add_le _ _
    _ ≤ KA / (n:ℝ) + KB / (n:ℝ) + KC / (n:ℝ) := by
        rw [abs_of_nonneg hBnn]
        have : |∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m| = ∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m := abs_of_nonneg hBnn
        linarith [hAbsA, hkB, hAbsTail]
    _ = (KA + KB + KC) / (n:ℝ) := by ring
