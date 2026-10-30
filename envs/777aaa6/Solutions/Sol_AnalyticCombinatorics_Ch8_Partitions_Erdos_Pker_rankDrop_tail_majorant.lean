-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.Pker_rankDrop_tail_majorant
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:41:52.590567+00:00
-- url     : https://prove2.me/submissions/fbedbec0-65e6-47d0-ba14-6df4f101c728

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RankDropKer
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdosWeight_nonneg_of_lt
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_kernelMass_sub_one_rate
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

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# R7 Layer 1: instantiation of the renewal spine to the partition kernel

Defines the predecessor transition kernel `Pker n k = erdosWeight n (n−k)/kernelMass n`, the rank
`rnk n = ⌊3√n⌋` (`ρ=3` makes window steps strictly drop rank), and the residual `dres`.  Proves the
kernel facts that feed the banked spine (`rec_iter_bound`, `pot_le_block_sum_of_leave`): nonnegativity,
rank monotonicity, the recurrence-in-`P` form, the probability normalization, the residual bound
(block-summable via `DefectSummable`), and the leave-probability `≥ μ`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

lemma rnk_mono : Monotone rnk := by
  intro a b hab
  apply Nat.floor_mono
  have : Real.sqrt (a : ℝ) ≤ Real.sqrt (b : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hab)
  linarith

/-- Reflection `k ↦ n−k` on `Icc 1 (n−1)`. -/
lemma sum_Icc_reflect_sub (n : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 (n - 1), F (n - k) = ∑ m ∈ Finset.Icc 1 (n - 1), F m := by
  apply Finset.sum_nbij' (fun k => n - k) (fun m => n - m)
  · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
  · intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
  · intro k hk; rw [Finset.mem_Icc] at hk; omega
  · intro m hm; rw [Finset.mem_Icc] at hm; omega
  · intro k _; rfl

/-- Floor bounds tying `rnk n = ⌊3√n⌋` to `√n`: `rnk n ≤ 3√n < rnk n + 1`. -/
lemma rnk_sqrt_bounds (n : ℕ) :
    (rnk n : ℝ) ≤ 3 * Real.sqrt n ∧ 3 * Real.sqrt n < (rnk n : ℝ) + 1 := by
  unfold rnk
  exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# T2.1 (honest restatement): the rank-drop kernel and its exponential tail majorant

The pointwise rank-drop *local limit* `rankDropKer v d → p d` is FALSE for the floor rank
`rnk v = ⌊3√v⌋` (the drop-`d` set is a `y`-window whose edges oscillate with `frac(3√v)`).  The engine, however, does not consume that limit; it consumes a
one-sided pair:

* an **exponential tail majorant** of the rank-drop, uniform in `v` (this file, `Pker_rankDrop_tail_majorant`);
* a **phase-uniform per-drop minorization** `rankDropKer v 1, rankDropKer v 2 ≥ η` (the genuinely
  new analytic input; see the gap doc).

This file builds the tail majorant.  An *upper* bound on the rank-drop is unaffected by the floor
oscillation: a rank drop exceeding `A` forces a *large jump* `m ≳ (A/3)√v`, whose `erdosWeight`-mass
is exponentially small in `A` (banked block-majorant machinery `left_half_tail_sum_le_block_majorants`
for the bulk `2m ≤ v` half, and `right_half_kernel_sum_le` for the `2m > v` half).

`rankDropKer` is the rank-drop law of the predecessor kernel `Pker`; it is exactly the pushforward of
`Pker v ·` under the rank-drop `k ↦ rnk v - rnk k`.

Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close

/-- **Large drop ⟹ large jump.**  If the rank drops by more than `A` on a step `v → k` (`1 ≤ k < v`),
then the jump `m = v − k` exceeds `(A/3)·√v`.  (A drop bigger than `A` forces `3√k < rnk v − A ≤
3√v − A`, hence `√v − √k > A/3`, hence `v − k = (√v−√k)(√v+√k) > (A/3)√v`.)  An *upper* bound on the
drop in terms of the jump — unaffected by the floor oscillation. -/
lemma large_drop_forces_large_jump {v k A : ℕ} (hk1 : 1 ≤ k) (hkv : k < v)
    (hdrop : A < rnk v - rnk k) :
    ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < ((v - k : ℕ) : ℝ) := by
  have hkle : rnk k ≤ rnk v := rnk_mono (le_of_lt hkv)
  -- rnk k + A < rnk v in ℕ, hence in ℝ
  have hNlt : rnk k + A + 1 ≤ rnk v := by omega
  have hRlt : (rnk k : ℝ) + (A : ℝ) + 1 ≤ (rnk v : ℝ) := by exact_mod_cast hNlt
  have hvpos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (by omega : 0 < v)
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hsv : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hvpos
  have hsk : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  -- 3√k < rnk k + 1 ≤ rnk v − A, and rnk v ≤ 3√v
  have h3k : (3 : ℝ) * Real.sqrt (k : ℝ) < (rnk k : ℝ) + 1 := (rnk_sqrt_bounds k).2
  have h3v : (rnk v : ℝ) ≤ 3 * Real.sqrt (v : ℝ) := (rnk_sqrt_bounds v).1
  -- 3√k < 3√v − A
  have hgap3 : 3 * Real.sqrt (k : ℝ) < 3 * Real.sqrt (v : ℝ) - (A : ℝ) := by linarith
  have hgap : Real.sqrt (v : ℝ) - Real.sqrt (k : ℝ) > (A : ℝ) / 3 := by linarith
  -- m = v − k = (√v − √k)(√v + √k)
  have hcast : ((v - k : ℕ) : ℝ) = (v : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hkv)]
  have hprod : (Real.sqrt (v : ℝ) - Real.sqrt (k : ℝ))
      * (Real.sqrt (v : ℝ) + Real.sqrt (k : ℝ)) = (v : ℝ) - (k : ℝ) := by
    have e1 : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt hvpos.le
    have e2 : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hkpos.le
    nlinarith [e1, e2]
  rw [hcast, ← hprod]
  -- (√v − √k)(√v + √k) ≥ (A/3)·√v   since (√v − √k) > A/3 ≥ 0 and (√v + √k) ≥ √v > 0
  have hApos : (0 : ℝ) ≤ (A : ℝ) / 3 := by positivity
  nlinarith [hgap, hsv, hsk, hApos]

/-- The rank-drop tail `∑_{d > A} rankDropKer v d` regroups exactly as the `Pker`-mass over the set of
predecessors `k` whose rank-drop exceeds `A`. -/
lemma rankDropKer_tail_eq_mass (v A : ℕ) :
    (∑ d ∈ (Finset.range v).filter (A < ·), rankDropKer v d)
      = ∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v),
          Pker v k := by
  classical
  unfold rankDropKer
  -- make both an honest double sum over range v × range v of guarded terms
  have hLHS : (∑ d ∈ (Finset.range v).filter (A < ·),
        ∑ k ∈ (Finset.range v).filter (fun k => rnk v - rnk k = d), Pker v k)
      = ∑ d ∈ Finset.range v, ∑ k ∈ Finset.range v,
          (if A < d then (if rnk v - rnk k = d then Pker v k else 0) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases hAd : A < d
    · rw [if_pos hAd, Finset.sum_filter]
      exact Finset.sum_congr rfl (fun k _ => by rw [if_pos hAd])
    · rw [if_neg hAd, Finset.sum_eq_zero (fun k _ => by rw [if_neg hAd])]
  rw [hLHS, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- inner: ∑_{d ∈ range v} (if A < d then (if rnk v − rnk k = d then Pker v k else 0) else 0)
  by_cases hkv : A < rnk v - rnk k ∧ rnk v - rnk k < v
  · rw [if_pos hkv]
    rw [Finset.sum_eq_single (rnk v - rnk k)]
    · rw [if_pos hkv.1, if_pos rfl]
    · intro d _ hd
      by_cases hAd : A < d
      · rw [if_pos hAd, if_neg (by exact fun h => hd h.symm)]
      · rw [if_neg hAd]
    · intro hmem
      exact absurd (Finset.mem_range.mpr hkv.2) hmem
  · rw [if_neg hkv]
    refine Finset.sum_eq_zero (fun d hd => ?_)
    by_cases hAd : A < d
    · rw [if_pos hAd]
      by_cases hdd : rnk v - rnk k = d
      · exact absurd ⟨hdd ▸ hAd, hdd ▸ Finset.mem_range.mp hd⟩ hkv
      · rw [if_neg hdd]
    · rw [if_neg hAd]

/-- **Numerator mass in `m`-coordinates, dominated by a far-jump window.**  The `erdosWeight`-mass of
the predecessors with rank-drop `> A` is, after the reflection `k ↦ v − k`, dominated by the
`erdosWeight`-mass on the far window `{m : (A/3)√v < m}` (every drop-`>A` jump exceeds `(A/3)√v` by
`large_drop_forces_large_jump`). -/
lemma rankDrop_mass_le_far_window {v A : ℕ} (hv : 2 ≤ v) :
    (∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v),
        erdosWeight v (v - k))
      ≤ ∑ m ∈ Finset.Icc 1 (v - 1),
          (if ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ) then erdosWeight v m else 0) := by
  classical
  -- reflect k ↦ v − k onto the m-window sum, then enlarge the index set
  have hreflect :
      (∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v),
          erdosWeight v (v - k))
        = ∑ m ∈ Finset.Icc 1 (v - 1),
            (if A < rnk v - rnk (v - m) ∧ rnk v - rnk (v - m) < v
              then erdosWeight v m else 0) := by
    -- rewrite the filtered LHS as a masked sum over Icc 1 (v−1) in k, reflect to m
    have hLHS :
        (∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v),
            erdosWeight v (v - k))
          = ∑ k ∈ Finset.Icc 1 (v - 1),
              (if A < rnk v - rnk k ∧ rnk v - rnk k < v then erdosWeight v (v - k) else 0) := by
      rw [Finset.sum_filter]
      symm
      apply Finset.sum_subset_zero_on_sdiff
      · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
      · intro k hk
        rw [Finset.mem_sdiff, Finset.mem_range] at hk
        -- k ∈ range v but k ∉ Icc 1 (v−1) ⟹ k = 0
        have hk0 : k = 0 := by
          rcases Nat.eq_zero_or_pos k with h | h
          · exact h
          · exact absurd (Finset.mem_Icc.mpr ⟨h, by omega⟩) hk.2
        subst hk0
        by_cases hc : A < rnk v - rnk 0 ∧ rnk v - rnk 0 < v
        · rw [if_pos hc]
          have : rnk v - rnk 0 < v := hc.2
          -- rnk 0 = 0, so A < rnk v < v ⟹ but erdosWeight v (v−0) = erdosWeight v v = 0? not directly.
          -- instead: k = 0 means v − k = v, erdosWeight v v has (v−v)=0 divisor; use erdosWeight def
          simp only [erdosWeight, Nat.sub_zero, Nat.sub_self, Nat.cast_zero, div_zero,
            zero_mul]
        · rw [if_neg hc]
      · intro k _; rfl
    rw [hLHS, ← sum_Icc_reflect_sub v
      (fun k => if A < rnk v - rnk k ∧ rnk v - rnk k < v then erdosWeight v (v - k) else 0)]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_Icc] at hm
    by_cases hc : A < rnk v - rnk (v - m) ∧ rnk v - rnk (v - m) < v
    · rw [if_pos hc, if_pos hc, show v - (v - m) = m by omega]
    · rw [if_neg hc, if_neg hc]
  rw [hreflect]
  refine Finset.sum_le_sum (fun m hm => ?_)
  rw [Finset.mem_Icc] at hm
  by_cases hc : A < rnk v - rnk (v - m) ∧ rnk v - rnk (v - m) < v
  · rw [if_pos hc]
    -- drop > A at predecessor (v−m) forces (A/3)√v < m via large_drop_forces_large_jump
    have hm1 : 1 ≤ v - m := by omega
    have hmv : v - m < v := by omega
    have hjump := large_drop_forces_large_jump (v := v) (k := v - m) (A := A) hm1 hmv hc.1
    rw [show v - (v - m) = m by omega] at hjump
    rw [if_pos hjump]
  · rw [if_neg hc]
    by_cases hc2 : ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ)
    · rw [if_pos hc2]; exact erdosWeight_nonneg_of_mem (Finset.mem_Icc.mpr hm)
    · rw [if_neg hc2]

/-- The convergent geometric-quadratic constant `G = ∑'_j (j+1)²·exp(−C/2)^j`. -/
noncomputable def rankDropG : ℝ := ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * Real.exp (-(C / 2)) ^ j

lemma rankDropG_nonneg : 0 ≤ rankDropG :=
  tsum_nonneg (fun j => by positivity)

/-- **Far-window split bound.**  For `v` with `2 ≤ v` and the eventual poly-beats-exp slack
`(v:ℝ)³ ≤ exp((C/20)√v)`, the `erdosWeight`-mass on the far window `{m : (A/3)√v < m}` splits into a
left (`2m ≤ v`) block-majorant tail and a right (`2m > v`) half-kernel tail. -/
lemma far_window_split_le {v A : ℕ} (hv : 0 < v) :
    (∑ m ∈ Finset.Icc 1 (v - 1),
        (if ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ) then erdosWeight v m else 0))
      ≤ (∑ m ∈ Finset.Icc 1 (v - 1),
            (if (⌊(A : ℝ) / 3⌋₊ : ℝ) * Real.sqrt (v : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ v
              then erdosWeight v m else 0))
        + (∑ m ∈ Finset.Icc 1 (v - 1), (if v < 2 * m then erdosWeight v m else 0)) := by
  classical
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun m hm => ?_)
  rw [Finset.mem_Icc] at hm
  have hew : 0 ≤ erdosWeight v m := erdosWeight_nonneg_of_mem (Finset.mem_Icc.mpr hm)
  by_cases hfar : ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ)
  · rw [if_pos hfar]
    rcases le_or_gt (2 * m) v with h2 | h2
    · -- left half: ⌊A/3⌋√v ≤ (A/3)√v < m
      have hKle : (⌊(A : ℝ) / 3⌋₊ : ℝ) * Real.sqrt (v : ℝ) ≤ (m : ℝ) := by
        have hfloor : (⌊(A : ℝ) / 3⌋₊ : ℝ) ≤ (A : ℝ) / 3 := Nat.floor_le (by positivity)
        have hsv : 0 ≤ Real.sqrt (v : ℝ) := Real.sqrt_nonneg _
        nlinarith [hfar, mul_le_mul_of_nonneg_right hfloor hsv]
      rw [if_pos ⟨hKle, h2⟩, if_neg (by omega : ¬ v < 2 * m)]
      linarith
    · -- right half
      rw [if_pos h2]
      by_cases hKL : (⌊(A : ℝ) / 3⌋₊ : ℝ) * Real.sqrt (v : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ v
      · exact absurd hKL.2 (by omega)
      · rw [if_neg hKL]; linarith
  · rw [if_neg hfar]
    refine add_nonneg ?_ ?_
    · split <;> [exact hew; exact le_refl 0]
    · split <;> [exact hew; exact le_refl 0]

/-- **Left-half block-majorant bound.**  The bulk (`2m ≤ v`) far-window mass at threshold index
`K = ⌊A/3⌋` is bounded by the banked geometric-quadratic block tail. -/
lemma left_block_tail_le {v : ℕ} (hv : 0 < v) (K : ℕ) :
    (∑ m ∈ Finset.Icc 1 (v - 1),
        (if (K : ℝ) * Real.sqrt (v : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ v then erdosWeight v m else 0))
      ≤ 2 * sigmaQuadConst * ((K : ℝ) + 1) ^ 2 * rankDropG * Real.exp (-(C / 2) * (K : ℝ)) := by
  calc (∑ m ∈ Finset.Icc 1 (v - 1),
          (if (K : ℝ) * Real.sqrt (v : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ v then erdosWeight v m else 0))
      ≤ ∑ k ∈ Finset.range (numBlocks v), if K ≤ k then leftBlockMajorant k else 0 :=
        left_half_tail_sum_le_block_majorants v K hv
    _ ≤ ∑' j : ℕ, leftBlockMajorant (j + K) :=
        finite_block_majorant_tail_le_shifted_tsum (numBlocks v) K
    _ ≤ 2 * sigmaQuadConst * ((K : ℝ) + 1) ^ 2 * rankDropG * Real.exp (-(C / 2) * (K : ℝ)) :=
        leftBlockMajorant_shifted_tsum_le K

/-- Elementary sup-bound: for `c > 0` and `x ≥ 0`, `(x+1)·e^{−cx} ≤ 1/c + 1`. -/
lemma succ_mul_exp_neg_le {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    (x + 1) * Real.exp (-c * x) ≤ 1 / c + 1 := by
  have hexp : c * x + 1 ≤ Real.exp (c * x) := by
    have := Real.add_one_le_exp (c * x); linarith
  have hepos : 0 < Real.exp (c * x) := Real.exp_pos _
  have he1 : (1 : ℝ) ≤ Real.exp (c * x) :=
    Real.one_le_exp_iff.mpr (by positivity)
  -- x + 1 ≤ (1/c + 1)·e^{cx}
  have hkey : x + 1 ≤ (1 / c + 1) * Real.exp (c * x) := by
    have hcx : c * x ≤ Real.exp (c * x) - 1 := by linarith
    have hx_le : x ≤ (Real.exp (c * x) - 1) / c := by
      rw [le_div_iff₀ hc]; nlinarith [hcx]
    have hdiv : (Real.exp (c * x) - 1) / c ≤ Real.exp (c * x) / c := by
      gcongr
      linarith
    have hexpand : (1 / c + 1) * Real.exp (c * x)
        = Real.exp (c * x) / c + Real.exp (c * x) := by ring
    rw [hexpand]
    linarith [hx_le, hdiv, he1]
  -- multiply by e^{−cx}
  have hrw : Real.exp (-c * x) = (Real.exp (c * x))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [hrw, mul_inv_le_iff₀ hepos]
  exact hkey

/-- **Left-half constant bound.**  `2σQ(⌊A/3⌋+1)²·G·e^{−(C/2)⌊A/3⌋} ≤ C_L·(A+1)·e^{−(C/60)A}` with
`C_L := 4σQ·G·e^{C/3}·(20/(3C)+1)`. -/
lemma left_block_const_bound (A : ℕ) :
    2 * sigmaQuadConst * ((⌊(A : ℝ) / 3⌋₊ : ℝ) + 1) ^ 2 * rankDropG
        * Real.exp (-(C / 2) * (⌊(A : ℝ) / 3⌋₊ : ℝ))
      ≤ (2 * sigmaQuadConst * rankDropG * Real.exp (C / 2) * (20 / (3 * C) + 1))
          * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
  have hC := C_pos
  have hsQ := sigmaQuadConst_pos
  have hG := rankDropG_nonneg
  set j : ℝ := (⌊(A : ℝ) / 3⌋₊ : ℝ) with hjdef
  have hj0 : 0 ≤ j := by positivity
  have hAle : 3 * j ≥ (A : ℝ) - 3 := by
    have hfl : (A : ℝ) / 3 < j + 1 := by
      have := Nat.lt_floor_add_one ((A : ℝ) / 3); rw [← hjdef] at this; exact this
    linarith
  have hjub : j + 1 ≤ (A : ℝ) + 1 := by
    have hflub : j ≤ (A : ℝ) / 3 := Nat.floor_le (by positivity)
    have hA0 : (0 : ℝ) ≤ (A : ℝ) := by positivity
    linarith
  -- e^{−(C/2)j} ≤ e^{C/3}·e^{−(C/6)A}
  have hexpj : Real.exp (-(C / 2) * j) ≤ Real.exp (C / 2) * Real.exp (-(C / 6) * (A : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hAle, hC]
  -- (j+1)² ≤ (A+1)²
  have hsq : (j + 1) ^ 2 ≤ ((A : ℝ) + 1) ^ 2 := by
    have h0 : (0 : ℝ) ≤ j + 1 := by linarith
    nlinarith [hjub, h0]
  -- (A+1)²·e^{−(C/6)A} ≤ (20/(3C)+1)·(A+1)·e^{−(C/60)A}
  have hsucc : ((A : ℝ) + 1) * Real.exp (-(3 * C / 20) * (A : ℝ)) ≤ 20 / (3 * C) + 1 := by
    have h := succ_mul_exp_neg_le (c := 3 * C / 20) (x := (A : ℝ)) (by positivity) (by positivity)
    have hrw : (1 : ℝ) / (3 * C / 20) = 20 / (3 * C) := by
      rw [div_div_eq_mul_div, one_mul]
    rw [hrw] at h; exact h
  have hsplit : ((A : ℝ) + 1) ^ 2 * Real.exp (-(C / 6) * (A : ℝ))
      ≤ (20 / (3 * C) + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
    have hfac : Real.exp (-(C / 6) * (A : ℝ))
        = Real.exp (-(3 * C / 20) * (A : ℝ)) * Real.exp (-(C / 60) * (A : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hfac]
    have hA1 : (0 : ℝ) ≤ (A : ℝ) + 1 := by positivity
    have he : (0 : ℝ) ≤ Real.exp (-(C / 60) * (A : ℝ)) := (Real.exp_pos _).le
    calc ((A : ℝ) + 1) ^ 2 * (Real.exp (-(3 * C / 20) * (A : ℝ)) * Real.exp (-(C / 60) * (A : ℝ)))
        = (((A : ℝ) + 1) * Real.exp (-(3 * C / 20) * (A : ℝ)))
            * (((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ))) := by ring
      _ ≤ (20 / (3 * C) + 1) * (((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ))) := by
            apply mul_le_mul_of_nonneg_right hsucc
            exact mul_nonneg hA1 he
      _ = (20 / (3 * C) + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by ring
  -- assemble
  have hC0 : (0 : ℝ) ≤ 2 * sigmaQuadConst * rankDropG := by positivity
  calc 2 * sigmaQuadConst * (j + 1) ^ 2 * rankDropG * Real.exp (-(C / 2) * j)
      = (2 * sigmaQuadConst * rankDropG) * ((j + 1) ^ 2 * Real.exp (-(C / 2) * j)) := by ring
    _ ≤ (2 * sigmaQuadConst * rankDropG)
          * (((A : ℝ) + 1) ^ 2 * (Real.exp (C / 2) * Real.exp (-(C / 6) * (A : ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          have hb : (0 : ℝ) ≤ ((A : ℝ) + 1) ^ 2 := by positivity
          exact mul_le_mul hsq hexpj (Real.exp_nonneg _) hb
    _ = (2 * sigmaQuadConst * rankDropG * Real.exp (C / 2))
          * (((A : ℝ) + 1) ^ 2 * Real.exp (-(C / 6) * (A : ℝ))) := by ring
    _ ≤ (2 * sigmaQuadConst * rankDropG * Real.exp (C / 2))
          * ((20 / (3 * C) + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ))) := by
          apply mul_le_mul_of_nonneg_left hsplit
          positivity
    _ = (2 * sigmaQuadConst * rankDropG * Real.exp (C / 2) * (20 / (3 * C) + 1))
          * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Topology BigOperators
open AnalyticCombinatorics.Ch8.Partitions.Erdos.Close
theorem solution :
    ∃ (γ : ℝ) (C₀ : ℝ), 0 < γ ∧ ∀ᶠ v : ℕ in atTop, ∀ A : ℕ,
        (∑ d ∈ (Finset.range v).filter (A < ·), rankDropKer v d)
          ≤ C₀ * ((A : ℝ) + 1) * Real.exp (-γ * (A : ℝ)) := by
  have hC := C_pos
  have hsQ := sigmaQuadConst_pos
  have hG := rankDropG_nonneg
  set CL : ℝ := 2 * sigmaQuadConst * rankDropG * Real.exp (C / 2) * (20 / (3 * C) + 1) with hCLdef
  have hCLnn : 0 ≤ CL := by rw [hCLdef]; positivity
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  -- eventual: kernelMass ≥ 1/2
  have hhalf : ∀ᶠ v : ℕ in atTop, K / (v : ℝ) ≤ 1 / 2 := by
    have htend : Tendsto (fun v : ℕ => K / (v : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    exact htend.eventually_le_const (by norm_num)
  -- slack: v³ e^{−(C/20)√v} ≤ 1/v ≤ 1
  have hslack := poly_mul_exp_neg_sqrt_le_inv (C / 20) (by linarith) 3
  refine ⟨C / 60, 2 * (CL + 1), by positivity, ?_⟩
  filter_upwards [hKev, hhalf, hslack, eventually_ge_atTop 2] with v hKv hhalfv hslackv hv2
  intro A
  have hv0 : 0 < v := by omega
  have hvR : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast (by omega : 1 ≤ v)
  have hvpos : (0 : ℝ) < (v : ℝ) := by linarith
  have hsv : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hvpos
  -- kernelMass ≥ 1/2
  obtain ⟨hSlo, _⟩ := abs_le.1 hKv
  have hSge : (1 : ℝ) / 2 ≤ kernelMass v := by linarith [hhalfv]
  have hSpos : (0 : ℝ) < kernelMass v := by linarith
  -- the tail = Pker-mass over drop>A ≤ 2·(erdosWeight far mass)
  rw [rankDropKer_tail_eq_mass]
  have hew_nn : ∀ m, 0 ≤ erdosWeight v m := by
    intro m
    unfold erdosWeight
    exact mul_nonneg (div_nonneg (sigmaR_nonneg m) (by positivity)) (Real.exp_nonneg _)
  have hPker_le : ∀ k, Pker v k ≤ 2 * erdosWeight v (v - k) := by
    intro k
    rcases Nat.lt_or_ge k v with hkv | hkv
    · rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · have hP0 : Pker v k = 0 := by unfold Pker; rw [if_neg (by omega)]
        rw [hP0]; linarith [hew_nn (v - k)]
      · have hPeq : Pker v k = erdosWeight v (v - k) / kernelMass v := by
          unfold Pker; rw [if_pos ⟨hk1, hkv⟩]
        rw [hPeq, div_le_iff₀ hSpos]
        nlinarith [hew_nn (v - k), hSge]
    · have hP0 : Pker v k = 0 := by unfold Pker; rw [if_neg (by omega)]
      rw [hP0]; linarith [hew_nn (v - k)]
  have hmass_le :
      (∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v), Pker v k)
        ≤ 2 * ∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v),
              erdosWeight v (v - k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hPker_le k)
  refine le_trans hmass_le ?_
  -- now bound 2·(erdosWeight far mass)
  set FW := ∑ k ∈ (Finset.range v).filter (fun k => A < rnk v - rnk k ∧ rnk v - rnk k < v),
              erdosWeight v (v - k) with hFWdef
  -- FW ≤ ∑_{m: (A/3)√v < m} erdosWeight
  have hFWwin : FW ≤ ∑ m ∈ Finset.Icc 1 (v - 1),
        (if ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ) then erdosWeight v m else 0) :=
    rankDrop_mass_le_far_window (by omega)
  rcases lt_or_ge (A : ℝ) (3 * Real.sqrt (v : ℝ)) with hAlt | hAge
  · -- A < 3√v : split into left + right
    have hsplit := far_window_split_le (v := v) (A := A) hv0
    -- left bound
    have hleft := left_block_tail_le (v := v) hv0 (⌊(A : ℝ) / 3⌋₊)
    have hleftconst := left_block_const_bound A
    -- right bound: v³ e^{−(C/10)√v} ≤ e^{−(C/20)√v} ≤ e^{−(C/60)A} ≤ (A+1)e^{−(C/60)A}
    have hright0 := right_half_kernel_sum_le v
    have hrwin : (v : ℝ) ^ 3 * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) ≤ 1 := by
      calc (v : ℝ) ^ 3 * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) ≤ 1 / (v : ℝ) := hslackv
        _ ≤ 1 := by rw [div_le_one hvpos]; exact hvR
    have hright1 : (v : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (v : ℝ))
        ≤ Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) := by
      have hfac : Real.exp (-(C / 10) * Real.sqrt (v : ℝ))
          = Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hfac]
      calc (v : ℝ) ^ 3 * (Real.exp (-(C / 20) * Real.sqrt (v : ℝ))
              * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)))
          = ((v : ℝ) ^ 3 * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)))
              * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) := by ring
        _ ≤ 1 * Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) :=
            mul_le_mul_of_nonneg_right hrwin (Real.exp_nonneg _)
        _ = Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) := by ring
    have hright2 : Real.exp (-(C / 20) * Real.sqrt (v : ℝ)) ≤ Real.exp (-(C / 60) * (A : ℝ)) := by
      apply Real.exp_le_exp.mpr
      -- −(C/20)√v ≤ −(C/60)A  ⟺  (C/60)A ≤ (C/20)√v  ⟸  A ≤ 3√v
      nlinarith [hAlt, hC, hsv]
    have hrightfin : (∑ m ∈ Finset.Icc 1 (v - 1), (if v < 2 * m then erdosWeight v m else 0))
        ≤ ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
      have hA1 : (1 : ℝ) ≤ (A : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (A : ℝ) := by positivity
        linarith
      calc (∑ m ∈ Finset.Icc 1 (v - 1), (if v < 2 * m then erdosWeight v m else 0))
          ≤ (v : ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (v : ℝ)) := hright0
        _ ≤ Real.exp (-(C / 60) * (A : ℝ)) := le_trans hright1 hright2
        _ ≤ ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
            nlinarith [hA1, Real.exp_nonneg (-(C / 60) * (A : ℝ))]
    -- combine: FW ≤ left + right ≤ CL(A+1)e^{−γA} + (A+1)e^{−γA} = (CL+1)(A+1)e^{−γA}
    have hFWtotal : FW ≤ (CL + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
      calc FW ≤ ∑ m ∈ Finset.Icc 1 (v - 1),
                (if ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ) then erdosWeight v m else 0) := hFWwin
        _ ≤ _ := hsplit
        _ ≤ (2 * sigmaQuadConst * ((⌊(A : ℝ) / 3⌋₊ : ℝ) + 1) ^ 2 * rankDropG
                * Real.exp (-(C / 2) * (⌊(A : ℝ) / 3⌋₊ : ℝ)))
              + ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
            apply add_le_add hleft hrightfin
        _ ≤ CL * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ))
              + ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
            have hL : 2 * sigmaQuadConst * ((⌊(A : ℝ) / 3⌋₊ : ℝ) + 1) ^ 2 * rankDropG
                  * Real.exp (-(C / 2) * (⌊(A : ℝ) / 3⌋₊ : ℝ))
                ≤ CL * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by
              rw [hCLdef]; exact hleftconst
            linarith [hL]
        _ = (CL + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by ring
    calc 2 * FW ≤ 2 * ((CL + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ))) := by
          linarith [hFWtotal]
      _ = 2 * (CL + 1) * ((A : ℝ) + 1) * Real.exp (-(C / 60) * (A : ℝ)) := by ring
  · -- A ≥ 3√v : far window empty, FW = 0
    have hFW0 : FW ≤ 0 := by
      refine le_trans hFWwin ?_
      apply le_of_eq
      refine Finset.sum_eq_zero (fun m hm => ?_)
      rw [Finset.mem_Icc] at hm
      have hmle : (m : ℝ) ≤ (v : ℝ) - 1 := by
        have : (m : ℝ) ≤ ((v - 1 : ℕ) : ℝ) := by exact_mod_cast hm.2
        rwa [Nat.cast_sub (by omega), Nat.cast_one] at this
      have hnot : ¬ ((A : ℝ) / 3) * Real.sqrt (v : ℝ) < (m : ℝ) := by
        push_neg
        -- (A/3)√v ≥ √v·√v = v > m
        have hAge3 : Real.sqrt (v : ℝ) ≤ (A : ℝ) / 3 := by linarith [hAge]
        have hvv : Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ) = (v : ℝ) :=
          Real.mul_self_sqrt hvpos.le
        nlinarith [hAge3, hsv, hmle, hvv]
      rw [if_neg hnot]
    have hFWnn : 0 ≤ FW := by
      rw [hFWdef]
      exact Finset.sum_nonneg (fun k _ => hew_nn (v - k))
    have hFWzero : FW = 0 := le_antisymm hFW0 hFWnn
    rw [hFWzero, mul_zero]
    have hexpnn : (0 : ℝ) ≤ Real.exp (-(C / 60) * (A : ℝ)) := Real.exp_nonneg _
    have hA1 : (0 : ℝ) ≤ (A : ℝ) + 1 := by positivity
    have : (0 : ℝ) ≤ 2 * (CL + 1) * ((A : ℝ) + 1) :=
      mul_nonneg (by linarith [hCLnn]) hA1
    exact mul_nonneg this hexpnn
