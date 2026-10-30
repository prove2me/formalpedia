-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.muNum_far_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:22:13.567892+00:00
-- url     : https://prove2.me/submissions/7b11fbc0-3c54-48c1-a415-11e283cbb8e5

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdosWeight_nonneg_of_lt
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

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Weighted far-erdos tail: helper lemmas

Sub-lemmas adapted from `ErdosKernelClose.lean` with `(m:ℝ)` weight.
The capstone `weighted_far_erdos_tail_le` is pending.
Opus-authored.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos
open Close

private lemma summable_succ_cube_geometric {q : ℝ} (hqpos : 0 < q) (hqlt1 : q < 1) :
    Summable (fun j : ℕ => (((j : ℕ).succ : ℝ) ^ 3) * q ^ j) := by
  have hnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact hqlt1
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hnorm
  have hsum_succ : Summable (fun j : ℕ => (((j : ℕ).succ : ℝ) ^ 3) * q ^ (j.succ)) :=
    h.comp_injective Nat.succ_injective
  refine (hsum_succ.mul_right q⁻¹).congr (fun j => ?_)
  rw [pow_succ' q j]
  field_simp [hqpos.ne']

private lemma shifted_cube_le (j K : ℕ) :
    (((j + K : ℕ) + 1 : ℝ) ^ 3) ≤
      (((j : ℕ).succ : ℝ) ^ 3) * (((K : ℝ) + 1) ^ 3) := by
  have hle : (((j + K : ℕ) + 1 : ℝ)) ≤ (((j : ℕ).succ : ℝ) * ((K : ℝ) + 1)) := by
    push_cast
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ)),
      (Nat.cast_nonneg K : (0 : ℝ) ≤ (K : ℝ)),
      mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))
        (Nat.cast_nonneg K : (0 : ℝ) ≤ (K : ℝ))]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (((j + K : ℕ) + 1 : ℝ))) hle 3
  calc
    (((j + K : ℕ) + 1 : ℝ) ^ 3) ≤
        (((j : ℕ).succ : ℝ) * ((K : ℝ) + 1)) ^ 3 := hpow
    _ = (((j : ℕ).succ : ℝ) ^ 3) * (((K : ℝ) + 1) ^ 3) := by ring

private lemma summable_shifted_cube_geometric {q : ℝ} (hqpos : 0 < q) (hqlt1 : q < 1)
    (K : ℕ) :
    Summable (fun j : ℕ => (((j + K : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := by
  have hsum : Summable (fun j : ℕ => (((j : ℕ).succ : ℝ) ^ 3) * q ^ j) :=
    summable_succ_cube_geometric hqpos hqlt1
  have hineq : ∀ j : ℕ,
      (((j + K : ℕ) + 1 : ℝ) ^ 3) * q ^ j ≤
        (((j : ℕ).succ : ℝ) ^ 3) * (((K : ℝ) + 1) ^ 3) * q ^ j := by
    intro j
    exact mul_le_mul_of_nonneg_right (shifted_cube_le j K) (by positivity)
  have hpos_shift : ∀ j : ℕ, 0 ≤ (((j + K : ℕ) + 1 : ℝ) ^ 3) * q ^ j := by
    intro j
    positivity
  refine Summable.of_nonneg_of_le hpos_shift hineq ?_
  simpa [Pi.mul_def, mul_assoc, mul_comm, mul_left_comm] using
    hsum.mul_right (((K : ℝ) + 1) ^ 3)

/-- `m ∈ block k` ⟹ `m ≤ (k+1)·√n`. -/
lemma m_le_block_bound {n m k : ℕ} (hn : 0 < n) (hmk : blockIndex n m = k) :
    (m : ℝ) ≤ (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := by
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hfloor_lt : (m : ℝ) / Real.sqrt (n : ℝ) < (k : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((m : ℝ) / Real.sqrt (n : ℝ))
    have hfloor_eq : ⌊(m : ℝ) / Real.sqrt (n : ℝ)⌋₊ = k := by
      simpa [blockIndex] using hmk
    simpa [hfloor_eq, Nat.cast_add, Nat.cast_one] using h
  have hmul : (m : ℝ) / Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) ≤ ((k : ℝ) + 1) * Real.sqrt (n : ℝ) :=
    mul_le_mul_of_nonneg_right hfloor_lt.le hsqrt_pos.le
  have hsimpl : (m : ℝ) / Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (m : ℝ) := by
    field_simp [hsqrt_pos.ne']
  rw [hsimpl] at hmul
  simpa [Nat.cast_add] using hmul

/-- Per-block weighted bound. -/
lemma weighted_kernel_block_left_half_le (n k : ℕ) (hn : 0 < n) :
    (∑ m ∈ (Finset.Icc 1 (n - 1)).filter
      (fun m => blockIndex n m = k ∧ 2 * m ≤ n),
      erdosWeight n m * (m : ℝ))
    ≤ leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := by
  classical
  let s := (Finset.Icc 1 (n - 1)).filter
    (fun m => blockIndex n m = k ∧ 2 * m ≤ n)
  have hterm_le : ∀ m ∈ s,
      erdosWeight n m * (m : ℝ) ≤ erdosWeight n m * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := by
    intro m hm
    have hmf : m ∈ (Finset.Icc 1 (n - 1)).filter
        (fun m => blockIndex n m = k ∧ 2 * m ≤ n) := by simpa [s] using hm
    have hmk : blockIndex n m = k := (Finset.mem_filter.mp hmf).2.1
    exact mul_le_mul_of_nonneg_left (m_le_block_bound hn hmk)
      (Erdos.erdosWeight_nonneg_of_mem (Finset.mem_filter.mp hmf).1)
  have hsum_le : (∑ m ∈ s, erdosWeight n m * (m : ℝ))
      ≤ ∑ m ∈ s, erdosWeight n m * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) :=
    Finset.sum_le_sum hterm_le
  have hfactor : (∑ m ∈ s, erdosWeight n m * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)))
      = (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) * (∑ m ∈ s, erdosWeight n m) := by
    rw [← Finset.sum_mul, mul_comm]
  have hblock : (∑ m ∈ s, erdosWeight n m) ≤ leftBlockMajorant k := by
    simpa [s, leftBlockMajorant] using kernel_block_left_half_le n k hn
  have hcoef_nonneg : 0 ≤ (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := by positivity
  calc
    (∑ m ∈ s, erdosWeight n m * (m : ℝ))
        ≤ ∑ m ∈ s, erdosWeight n m * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := hsum_le
    _ = (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) * (∑ m ∈ s, erdosWeight n m) := hfactor
    _ ≤ (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) * leftBlockMajorant k :=
      mul_le_mul_of_nonneg_left hblock hcoef_nonneg
    _ = leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) := by ring

/-- Weighted adaptation of `left_half_tail_sum_le_block_majorants`. -/
lemma weighted_left_half_tail_sum_le_block_majorants (n K : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
      if (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ n
      then erdosWeight n m * (m : ℝ)
      else 0)
    ≤ ∑ k ∈ Finset.range (numBlocks n),
        if K ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ))
        else 0 := by
  classical
  let f : ℕ → ℝ := fun m =>
    if (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ) ∧ 2 * m ≤ n
    then erdosWeight n m * (m : ℝ) else 0
  have hdecomp := block_decomposition n f
  rw [hdecomp]
  refine Finset.sum_le_sum (fun k _ => ?_)
  by_cases hKk : K ≤ k
  · have hterm_le : ∀ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
        f m ≤ if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0 := by
      intro m hm
      have hmI : m ∈ Finset.Icc 1 (n - 1) := (Finset.mem_filter.mp hm).1
      by_cases hhalf : 2 * m ≤ n
      · by_cases htail : (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ)
        · simp [f, htail, hhalf]
        · simp [f, htail, hhalf]
          exact mul_nonneg (Erdos.erdosWeight_nonneg_of_mem hmI) (by positivity)
      · simp [f, hhalf]
    have hsum_le_half : (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m)
        ≤ ∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
          if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0 :=
      Finset.sum_le_sum hterm_le
    have hhalf_eq : (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
          if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0)
        = ∑ m ∈ (Finset.Icc 1 (n - 1)).filter
            (fun m => blockIndex n m = k ∧ 2 * m ≤ n),
          erdosWeight n m * (m : ℝ) := by
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      by_cases hb : blockIndex n m = k
      · by_cases hh : 2 * m ≤ n <;> simp [hb, hh]
      · simp [hb]
    calc
      (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m)
          ≤ ∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
            if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0 := hsum_le_half
      _ = ∑ m ∈ (Finset.Icc 1 (n - 1)).filter
            (fun m => blockIndex n m = k ∧ 2 * m ≤ n),
          erdosWeight n m * (m : ℝ) := hhalf_eq
      _ ≤ leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) :=
        weighted_kernel_block_left_half_le n k hn
      _ = (if K ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) else 0) := by
        simp [hKk]
  · have hzero : ∀ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k),
        f m = 0 := by
      intro m hm
      by_cases htail : (K : ℝ) * Real.sqrt (n : ℝ) ≤ (m : ℝ)
      · have hge := tail_block_index_ge (n := n) (K := K) (k := k) (m := m) hn hm htail
        exact False.elim (hKk hge)
      · simp [f, htail]
    calc
      (∑ m ∈ (Finset.Icc 1 (n - 1)).filter (fun m => blockIndex n m = k), f m) = 0 :=
        Finset.sum_eq_zero hzero
      _ ≤ (if K ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n : ℝ)) else 0) := by
        simp [hKk]

/-- Cubic moment H₃ = Σ (j+1)³·q^j. -/
noncomputable def tailH3 : ℝ :=
  ∑' j : ℕ, (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j

lemma tailH3_pos : 0 < tailH3 := by
  dsimp [tailH3]
  have hnonneg : ∀ j, 0 ≤ (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j := by
    intro j; positivity
  have hsumm : Summable (fun j : ℕ => (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j) :=
    summable_succ_cube_geometric (q := Real.exp (-(C / 2))) (Real.exp_pos _)
      (by rw [Real.exp_lt_one_iff]; nlinarith [C_pos])
  have h_first_le : 1 ≤ ∑' j : ℕ, (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j := by
    calc 1 = ((0 : ℕ).succ : ℝ)^3 * Real.exp (-(C / 2)) ^ 0 := by norm_num
      _ = (∑ j ∈ ({0} : Finset ℕ), (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j) := by simp
      _ ≤ ∑' j : ℕ, (((j : ℕ).succ : ℝ) ^ 3) * Real.exp (-(C / 2)) ^ j :=
        hsumm.sum_le_tsum ({0} : Finset ℕ) (by
          intro j hj; simp at hj; exact hnonneg j)
  have hpos_one : (0 : ℝ) < 1 := by norm_num
  have : 1 ≤ tailH3 := by
    dsimp [tailH3]; exact h_first_le
  linarith

lemma tailH3_nonneg : 0 ≤ tailH3 := tailH3_pos.le

/-- Weighted block-majorant shift identity. -/
lemma leftBlockMajorant_weighted_shifted_tsum_le (Kn : ℕ) (s : ℝ) (hs : 0 < s) :
    (∑' j : ℕ, leftBlockMajorant (j + Kn) * (((j + Kn : ℕ) + 1 : ℝ) * s))
    ≤ 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3
      * Real.exp (-(C / 2) * (Kn : ℝ)) * Real.exp (C / 2) := by
  set q := Real.exp (-(C / 2)) with hqdef
  have hqpos : 0 < q := by rw [hqdef]; exact Real.exp_pos _
  have hqlt1 : q < 1 := by
    rw [hqdef, Real.exp_lt_one_iff]
    nlinarith [C_pos]
  have hsum : Summable (fun j : ℕ => (((j : ℕ).succ : ℝ)^3) * q ^ j) :=
    summable_succ_cube_geometric hqpos hqlt1
  have hsum_shift : Summable (fun j : ℕ => (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) :=
    summable_shifted_cube_geometric hqpos hqlt1 Kn
  have hrewrite :
      (∑' j : ℕ, leftBlockMajorant (j + Kn) * (((j + Kn : ℕ) + 1 : ℝ) * s))
        = (2 * sigmaQuadConst * s * q ^ Kn) *
          (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := by
    calc
      (∑' j : ℕ, leftBlockMajorant (j + Kn) * (((j + Kn : ℕ) + 1 : ℝ) * s))
          = ∑' j : ℕ,
              (2 * sigmaQuadConst * s * q ^ Kn) *
                ((((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := by
            refine tsum_congr (fun j => ?_)
            rw [leftBlockMajorant, show Real.exp (-(C / 2) * ((j + Kn : ℕ) : ℝ))
                = q ^ (j + Kn) by
                  rw [hqdef, ← Real.exp_nat_mul]
                  congr 1
                  ring]
            rw [pow_add]
            norm_num [Nat.cast_add, Nat.cast_one]
            ring
      _ = (2 * sigmaQuadConst * s * q ^ Kn) *
          (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := by
            rw [hsum_shift.tsum_mul_left (2 * sigmaQuadConst * s * q ^ Kn)]
  have htail : (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j)
      ≤ ((Kn : ℝ) + 1) ^ 3 * tailH3 := by
    have hbound : ∀ j : ℕ,
        (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j ≤
          (((Kn : ℝ) + 1) ^ 3) * ((((j : ℕ).succ : ℝ) ^ 3) * q ^ j) := by
      intro j
      calc
        (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j
            ≤ ((((j : ℕ).succ : ℝ) ^ 3) * (((Kn : ℝ) + 1) ^ 3)) * q ^ j :=
              mul_le_mul_of_nonneg_right (shifted_cube_le j Kn) (by positivity)
        _ = (((Kn : ℝ) + 1) ^ 3) * ((((j : ℕ).succ : ℝ) ^ 3) * q ^ j) := by ring
    have hdom : Summable (fun j : ℕ =>
        (((Kn : ℝ) + 1) ^ 3) * ((((j : ℕ).succ : ℝ) ^ 3) * q ^ j)) :=
      hsum.mul_left (((Kn : ℝ) + 1) ^ 3)
    calc
      (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j)
          ≤ ∑' j : ℕ,
              (((Kn : ℝ) + 1) ^ 3) * ((((j : ℕ).succ : ℝ) ^ 3) * q ^ j) :=
            Summable.tsum_le_tsum hbound hsum_shift hdom
      _ = ((Kn : ℝ) + 1) ^ 3 *
            (∑' j : ℕ, (((j : ℕ).succ : ℝ) ^ 3) * q ^ j) := by
            rw [hsum.tsum_mul_left (((Kn : ℝ) + 1) ^ 3)]
      _ = ((Kn : ℝ) + 1) ^ 3 * tailH3 := by
            rw [tailH3, hqdef]
  have hcoef_nonneg : 0 ≤ 2 * sigmaQuadConst * s * q ^ Kn := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) sigmaQuadConst_pos.le) hs.le)
      (pow_nonneg hqpos.le Kn)
  have hmain :
      (2 * sigmaQuadConst * s * q ^ Kn) *
        (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j)
      ≤ (2 * sigmaQuadConst * s * q ^ Kn) * (((Kn : ℝ) + 1) ^ 3 * tailH3) :=
    mul_le_mul_of_nonneg_left htail hcoef_nonneg
  have hge_exp : (1 : ℝ) ≤ Real.exp (C / 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [C_pos])
  calc
    (∑' j : ℕ, leftBlockMajorant (j + Kn) * (((j + Kn : ℕ) + 1 : ℝ) * s))
        = (2 * sigmaQuadConst * s * q ^ Kn) *
            (∑' j : ℕ, (((j + Kn : ℕ) + 1 : ℝ) ^ 3) * q ^ j) := hrewrite
    _ ≤ (2 * sigmaQuadConst * s * q ^ Kn) * (((Kn : ℝ) + 1) ^ 3 * tailH3) := hmain
    _ = 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 * q ^ Kn := by ring
    _ = 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 *
          Real.exp (-(C / 2) * (Kn : ℝ)) := by
        rw [hqdef, ← Real.exp_nat_mul]
        congr 1
        ring
    _ ≤ 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 *
          Real.exp (-(C / 2) * (Kn : ℝ)) * Real.exp (C / 2) := by
        have hbase_nonneg : 0 ≤ 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) *
            tailH3 * Real.exp (-(C / 2) * (Kn : ℝ)) := by
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (mul_nonneg (by norm_num) sigmaQuadConst_pos.le) hs.le)
                (by positivity))
              tailH3_nonneg)
            (Real.exp_pos _).le
        calc
          2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 *
              Real.exp (-(C / 2) * (Kn : ℝ))
              = 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 *
                  Real.exp (-(C / 2) * (Kn : ℝ)) * 1 := by ring
          _ ≤ 2 * sigmaQuadConst * s * (((Kn : ℝ) + 1) ^ 3) * tailH3 *
              Real.exp (-(C / 2) * (Kn : ℝ)) * Real.exp (C / 2) :=
                mul_le_mul_of_nonneg_left hge_exp hbase_nonneg

/-- **Weighted far-erdos tail**: Σ_{m>⌊n^{2/3}⌋} erdosWeight·m ≤ const/n.
    Finite weighted block tails are bounded by the shifted weighted majorant tsum. -/
private lemma finite_weighted_block_majorant_tail_le_shifted_tsum (N K : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (∑ k ∈ Finset.range N,
      if K ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * s) else 0) ≤
      ∑' j : ℕ, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := by
  classical
  let t := (Finset.range N).filter (fun k => K ≤ k)
  have hsum_filter :
      (∑ k ∈ Finset.range N,
        if K ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * s) else 0) =
        ∑ k ∈ t, leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * s) := by
    simp [t, Finset.sum_filter]
  let imageS : Finset ℕ := t.image (fun k => k - K)
  have hinj : Set.InjOn (fun k : ℕ => k - K) (↑t : Set ℕ) := by
    intro a ha b hb hsub
    have hKa : K ≤ a := by
      have hmem : a ∈ t := by simpa using ha
      exact (Finset.mem_filter.mp hmem).2
    have hKb : K ≤ b := by
      have hmem : b ∈ t := by simpa using hb
      exact (Finset.mem_filter.mp hmem).2
    calc
      a = (a - K) + K := (Nat.sub_add_cancel hKa).symm
      _ = (b - K) + K := by
        rw [show a - K = b - K from hsub]
      _ = b := Nat.sub_add_cancel hKb
  have hreindex :
      (∑ k ∈ t, leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * s)) =
        ∑ j ∈ imageS, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := by
    dsimp [imageS]
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro k hk
      have hKk : K ≤ k := (Finset.mem_filter.mp hk).2
      have hk_eq : k - K + K = k := Nat.sub_add_cancel hKk
      simp [hk_eq]
    · intro a ha b hb h
      exact hinj (by simpa using ha) (by simpa using hb) h
  have himage_subset : imageS ⊆ Finset.range N := by
    intro j hj
    dsimp [imageS] at hj
    rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
    have hkN : k < N := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    exact Finset.mem_range.mpr (by omega)
  have hterm_nonneg : ∀ j : ℕ,
      0 ≤ leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := by
    intro j
    exact mul_nonneg (leftBlockMajorant_nonneg (j + K)) (mul_nonneg (by positivity) hs)
  have hfinite_le_range :
      (∑ j ∈ imageS, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) ) ≤
        ∑ j ∈ Finset.range N, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
      (fun j _hj _hnot => hterm_nonneg j)
  have hshift_summable :
      Summable fun j : ℕ => leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := by
    set q := Real.exp (-(C / 2)) with hqdef
    have hqpos : 0 < q := by rw [hqdef]; exact Real.exp_pos _
    have hqlt1 : q < 1 := by
      rw [hqdef, Real.exp_lt_one_iff]
      nlinarith [C_pos]
    have hsum_shift : Summable (fun j : ℕ => (((j + K : ℕ) + 1 : ℝ) ^ 3) * q ^ j) :=
      summable_shifted_cube_geometric hqpos hqlt1 K
    refine (hsum_shift.mul_left (2 * sigmaQuadConst * s * q ^ K)).congr (fun j => ?_)
    rw [leftBlockMajorant, show Real.exp (-(C / 2) * ((j + K : ℕ) : ℝ)) = q ^ (j + K) by
      rw [hqdef, ← Real.exp_nat_mul]
      congr 1
      ring]
    rw [pow_add]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  have hprefix_le_tsum :
      (∑ j ∈ Finset.range N, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s))) ≤
        ∑' j : ℕ, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := by
    exact hshift_summable.sum_le_tsum (Finset.range N) (fun j _hj => hterm_nonneg j)
  calc
    (∑ k ∈ Finset.range N,
      if K ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * s) else 0)
        = ∑ k ∈ t, leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * s) := hsum_filter
    _ = ∑ j ∈ imageS, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := hreindex
    _ ≤ ∑ j ∈ Finset.range N, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := hfinite_le_range
    _ ≤ ∑' j : ℕ, leftBlockMajorant (j + K) * ((((j + K : ℕ) + 1 : ℝ) * s)) := hprefix_le_tsum

/-- **Weighted far-erdos tail**: Σ_{m>⌊n^{2/3}⌋} erdosWeight·m ≤ const/n. -/
theorem weighted_far_erdos_tail_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Icc (⌊(n:ℝ) ^ (2/3 : ℝ)⌋₊ + 1) (n - 1), erdosWeight n m * (m : ℝ)) ≤ K / (n : ℝ) := by
  have hCpos := C_pos
  have hsQ : 0 ≤ sigmaQuadConst := sigmaQuadConst_pos.le
  have hH3 : 0 ≤ tailH3 := tailH3_nonneg
  have hKLnn : 0 ≤ 16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsQ) hH3) (Real.exp_pos _).le)
      (Real.exp_pos _).le
  refine ⟨1 + 16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) + 1,
    by linarith, ?_⟩
  filter_upwards [poly_mul_exp_neg_sqrt_le_inv (C / 10) (by linarith) 4,
    poly_mul_exp_neg_sixthRoot_le_inv (C / 2) (by linarith) 4,
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
  have hsplit : ∀ m : ℕ, erdosWeight n m * (m : ℝ)
      = (if n < 2 * m then erdosWeight n m * (m : ℝ) else 0) +
        (if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0) := by
    intro m
    rcases lt_or_ge n (2 * m) with h | h
    · rw [if_pos h, if_neg (by omega)]
      ring
    · rw [if_neg (by omega), if_pos h]
      ring
  rw [Finset.sum_congr rfl (fun m _ => hsplit m), Finset.sum_add_distrib]
  have hright : (∑ m ∈ Finset.Icc (M + 1) (n - 1),
      if n < 2 * m then erdosWeight n m * (m : ℝ) else 0) ≤ 1 / (n:ℝ) := by
    have h1 : (∑ m ∈ Finset.Icc (M + 1) (n - 1),
        if n < 2 * m then erdosWeight n m * (m : ℝ) else 0)
        ≤ (n:ℝ) ^ 4 * Real.exp (-(C / 10) * Real.sqrt (n:ℝ)) := by
      calc
        (∑ m ∈ Finset.Icc (M + 1) (n - 1),
          if n < 2 * m then erdosWeight n m * (m : ℝ) else 0)
            ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
                if n < 2 * m then erdosWeight n m * (m : ℝ) else 0 := by
              refine Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.Icc_subset_Icc (by omega) le_rfl) (fun m _ _ => ?_)
              split_ifs
              · exact mul_nonneg (hew_nn m) (by positivity)
              · exact le_rfl
        _ ≤ (n:ℝ) * (∑ m ∈ Finset.Icc 1 (n - 1),
                if n < 2 * m then erdosWeight n m else 0) := by
              calc
                (∑ m ∈ Finset.Icc 1 (n - 1),
                  if n < 2 * m then erdosWeight n m * (m : ℝ) else 0)
                    ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
                        (n:ℝ) * (if n < 2 * m then erdosWeight n m else 0) := by
                      refine Finset.sum_le_sum (fun m hm => ?_)
                      by_cases hrightm : n < 2 * m
                      · rw [if_pos hrightm, if_pos hrightm]
                        have hmn : m ≤ n := by
                          have hmle : m ≤ n - 1 := (Finset.mem_Icc.mp hm).2
                          omega
                        have hmreal : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
                        have hmul := mul_le_mul_of_nonneg_left hmreal (hew_nn m)
                        nlinarith
                      · rw [if_neg hrightm, if_neg hrightm]
                        positivity
                _ = (n:ℝ) * (∑ m ∈ Finset.Icc 1 (n - 1),
                        if n < 2 * m then erdosWeight n m else 0) := by
                      rw [Finset.mul_sum]
        _ ≤ (n:ℝ) * ((n:ℝ) ^ 3 * Real.exp (-(C / 10) * Real.sqrt (n:ℝ))) := by
              exact mul_le_mul_of_nonneg_left (right_half_kernel_sum_le n) (by positivity)
        _ = (n:ℝ) ^ 4 * Real.exp (-(C / 10) * Real.sqrt (n:ℝ)) := by ring
    linarith [h1, hsqrt]
  have hKn_le : (Kn:ℝ) ≤ (n:ℝ) ^ (1/6 : ℝ) := Nat.floor_le (by positivity)
  have h16le : (n:ℝ) ^ (1/6 : ℝ) ≤ (n:ℝ) := by
    calc
      (n:ℝ) ^ (1/6 : ℝ) ≤ (n:ℝ) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnge1 (by norm_num)
      _ = (n:ℝ) := Real.rpow_one _
  have hKnge : (n:ℝ) ^ (1/6 : ℝ) - 1 ≤ (Kn:ℝ) := by
    have := Nat.lt_floor_add_one ((n:ℝ) ^ (1/6 : ℝ))
    rw [← hKndef] at this
    linarith
  have hleft : (∑ m ∈ Finset.Icc (M + 1) (n - 1),
      if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0)
      ≤ 16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) * (1 / (n:ℝ)) := by
    have hcond : (∑ m ∈ Finset.Icc (M + 1) (n - 1),
        if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0)
        ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
            if (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (m:ℝ) ∧ 2 * m ≤ n
            then erdosWeight n m * (m : ℝ) else 0 := by
      calc
        (∑ m ∈ Finset.Icc (M + 1) (n - 1),
          if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0)
            ≤ ∑ m ∈ Finset.Icc (M + 1) (n - 1),
                if (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (m:ℝ) ∧ 2 * m ≤ n
                then erdosWeight n m * (m : ℝ) else 0 := by
              apply Finset.sum_le_sum
              intro m hm
              rw [Finset.mem_Icc] at hm
              have hKnm : (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (m:ℝ) := by
                have hm_gt : (n:ℝ) ^ (2/3 : ℝ) < (m:ℝ) := by
                  have hlt : (n:ℝ) ^ (2/3 : ℝ) < (M:ℝ) + 1 := by
                    have := Nat.lt_floor_add_one ((n:ℝ) ^ (2/3 : ℝ))
                    rw [← hMdef] at this
                    linarith
                  have hge : (M:ℝ) + 1 ≤ (m:ℝ) := by exact_mod_cast hm.1
                  linarith
                calc
                  (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (n:ℝ) ^ (1/6 : ℝ) * Real.sqrt (n:ℝ) :=
                    mul_le_mul_of_nonneg_right hKn_le (Real.sqrt_nonneg _)
                  _ = (n:ℝ) ^ (2/3 : ℝ) := by
                    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]
                    norm_num
                  _ ≤ (m:ℝ) := le_of_lt hm_gt
              by_cases h2 : 2 * m ≤ n
              · rw [if_pos h2, if_pos ⟨hKnm, h2⟩]
              · rw [if_neg h2, if_neg (fun h => h2 h.2)]
        _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Icc_subset_Icc (by omega) le_rfl) (fun m _ _ => ?_)
          split_ifs
          · exact mul_nonneg (hew_nn m) (by positivity)
          · exact le_rfl
    have hchain : (∑ m ∈ Finset.Icc 1 (n - 1),
        if (Kn:ℝ) * Real.sqrt (n:ℝ) ≤ (m:ℝ) ∧ 2 * m ≤ n
        then erdosWeight n m * (m : ℝ) else 0)
        ≤ 2 * sigmaQuadConst * Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) * tailH3
          * Real.exp (-(C / 2) * (Kn:ℝ)) * Real.exp (C / 2) := by
      calc
        _ ≤ ∑ k ∈ Finset.range (numBlocks n),
              if Kn ≤ k then leftBlockMajorant k * (((k + 1 : ℕ) : ℝ) * Real.sqrt (n:ℝ)) else 0 :=
            weighted_left_half_tail_sum_le_block_majorants n Kn hn0'
        _ ≤ ∑' j : ℕ, leftBlockMajorant (j + Kn) * ((((j + Kn : ℕ) + 1 : ℝ) * Real.sqrt (n:ℝ))) :=
            finite_weighted_block_majorant_tail_le_shifted_tsum (numBlocks n) Kn (Real.sqrt (n:ℝ))
              (Real.sqrt_nonneg _)
        _ ≤ _ := leftBlockMajorant_weighted_shifted_tsum_le Kn (Real.sqrt (n:ℝ)) hs0
    have hsqrt_le_n : Real.sqrt (n:ℝ) ≤ (n:ℝ) := by
      calc
        Real.sqrt (n:ℝ) = (n:ℝ) ^ (1/2 : ℝ) := by rw [Real.sqrt_eq_rpow]
        _ ≤ (n:ℝ) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hnge1 (by norm_num)
        _ = (n:ℝ) := Real.rpow_one _
    have hKn1le : (Kn:ℝ) + 1 ≤ 2 * (n:ℝ) := by
      nlinarith [hKn_le, h16le, hnge1]
    have hcubele : ((Kn:ℝ) + 1) ^ 3 ≤ 8 * (n:ℝ) ^ 3 := by
      have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (Kn:ℝ) + 1) hKn1le 3
      nlinarith
    have hpoly_le : Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) ≤ 8 * (n:ℝ) ^ 4 := by
      have hmul := mul_le_mul hsqrt_le_n hcubele
        (by positivity : 0 ≤ ((Kn:ℝ) + 1) ^ 3) (by positivity : 0 ≤ (n:ℝ))
      calc
        Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) ≤ (n:ℝ) * (8 * (n:ℝ) ^ 3) := hmul
        _ = 8 * (n:ℝ) ^ 4 := by ring
    have hexpKn : Real.exp (-(C / 2) * (Kn:ℝ))
        ≤ Real.exp (C / 2) * Real.exp (-(C / 2) * (n:ℝ) ^ (1/6 : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [hKnge, hCpos]
    have hKbound : Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) *
        Real.exp (-(C / 2) * (Kn:ℝ)) ≤ 8 * Real.exp (C / 2) * (1 / (n:ℝ)) := by
      calc
        Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) * Real.exp (-(C / 2) * (Kn:ℝ))
            ≤ (8 * (n:ℝ) ^ 4) *
                (Real.exp (C / 2) * Real.exp (-(C / 2) * (n:ℝ) ^ (1/6 : ℝ))) :=
              mul_le_mul hpoly_le hexpKn (Real.exp_pos _).le (by positivity)
        _ = 8 * Real.exp (C / 2) *
              ((n:ℝ) ^ 4 * Real.exp (-(C / 2) * (n:ℝ) ^ (1/6 : ℝ))) := by ring
        _ ≤ 8 * Real.exp (C / 2) * (1 / (n:ℝ)) :=
              mul_le_mul_of_nonneg_left hsixth (by positivity)
    have hcoef_nonneg : 0 ≤ 2 * sigmaQuadConst * tailH3 * Real.exp (C / 2) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsQ) hH3) (Real.exp_pos _).le
    calc
      (∑ m ∈ Finset.Icc (M + 1) (n - 1),
        if 2 * m ≤ n then erdosWeight n m * (m : ℝ) else 0)
          ≤ 2 * sigmaQuadConst * Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) * tailH3
              * Real.exp (-(C / 2) * (Kn:ℝ)) * Real.exp (C / 2) := le_trans hcond hchain
      _ = 2 * sigmaQuadConst * tailH3 * Real.exp (C / 2) *
            (Real.sqrt (n:ℝ) * (((Kn:ℝ) + 1) ^ 3) *
              Real.exp (-(C / 2) * (Kn:ℝ))) := by ring
      _ ≤ 2 * sigmaQuadConst * tailH3 * Real.exp (C / 2) *
            (8 * Real.exp (C / 2) * (1 / (n:ℝ))) :=
          mul_le_mul_of_nonneg_left hKbound hcoef_nonneg
      _ = 16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) * (1 / (n:ℝ)) := by ring
  have hfinal : 1 / (n:ℝ) +
      16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) * (1 / (n:ℝ))
      ≤ (1 + 16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) + 1) / (n:ℝ) := by
    rw [add_div, add_div]
    have h16 : 16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2) * (1 / (n:ℝ))
        = (16 * sigmaQuadConst * tailH3 * Real.exp (C / 2) * Real.exp (C / 2)) / (n:ℝ) := by ring
    rw [h16]
    linarith [show (0:ℝ) ≤ 1 / (n:ℝ) by positivity]
  linarith [hright, hleft, hfinal]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Assembly of the two-term expansion for `muNum`

This file only assembles the banked estimates:

* the infinite model two-term expansion,
* the two main-range errors,
* the weighted Erdős far tail,
* and a local model-product tail.
-/

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

private lemma rhoDrop_le_three_mul_div_sqrt {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    rhoDrop n m ≤ 3 * (m : ℝ) / Real.sqrt (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  set u : ℝ := Real.sqrt (((n - m : ℕ) : ℝ)) with hudef
  have hs0 : 0 < s := by
    rw [hsdef]
    exact Real.sqrt_pos.mpr hnpos
  have hs2 : s ^ 2 = (n : ℝ) := by
    rw [hsdef]
    exact Real.sq_sqrt hnpos.le
  have hu2 : u ^ 2 = ((n - m : ℕ) : ℝ) := by
    rw [hudef]
    exact Real.sq_sqrt (by positivity)
  have hus : u ≤ s := by
    rw [hudef, hsdef]
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.sub_le n m
  have hu0 : 0 ≤ u := by
    rw [hudef]
    exact Real.sqrt_nonneg _
  have hprod : u ^ 2 ≤ u * s := by
    calc u ^ 2 = u * u := by ring
      _ ≤ u * s := mul_le_mul_of_nonneg_left hus hu0
  have hsubadd : ((n - m : ℕ) : ℝ) + (m : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hm
  have hmul : (s - u) * s ≤ (m : ℝ) := by
    calc
      (s - u) * s = s ^ 2 - u * s := by ring
      _ ≤ s ^ 2 - u ^ 2 := by linarith
      _ = (m : ℝ) := by
        rw [hs2, hu2]
        linarith
  have hdrop : Real.sqrt (n : ℝ) - Real.sqrt (((n - m : ℕ) : ℝ))
      ≤ (m : ℝ) / Real.sqrt (n : ℝ) := by
    rw [← hsdef, ← hudef]
    rw [le_div_iff₀ hs0]
    exact hmul
  rw [rhoDrop]
  calc
    3 * (Real.sqrt (n : ℝ) - Real.sqrt (((n - m : ℕ) : ℝ)))
        ≤ 3 * ((m : ℝ) / Real.sqrt (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hdrop (by norm_num : (0 : ℝ) ≤ 3)
    _ = 3 * (m : ℝ) / Real.sqrt (n : ℝ) := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Finset
open scoped Topology BigOperators
theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc (⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ + 1) (n - 1),
        erdosWeight n m * rhoDrop n m) ≤ K / (n : ℝ) := by
  obtain ⟨K, hKpos, hK⟩ := weighted_far_erdos_tail_le
  refine ⟨3 * K, by positivity, ?_⟩
  filter_upwards [hK, Filter.eventually_ge_atTop 1] with n hKn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  have hcoef_le : 3 / Real.sqrt (n : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hs0]
    nlinarith
  set M : ℕ := ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ with hMdef
  have hpoint : ∀ m ∈ Finset.Icc (M + 1) (n - 1),
      erdosWeight n m * rhoDrop n m
        ≤ (3 / Real.sqrt (n : ℝ)) * (erdosWeight n m * (m : ℝ)) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmI : m ∈ Finset.Icc 1 (n - 1) := by
      rw [Finset.mem_Icc]
      omega
    have hmn : m ≤ n := by omega
    have hew : 0 ≤ erdosWeight n m := erdosWeight_nonneg_of_mem hmI
    have hrho := rhoDrop_le_three_mul_div_sqrt hn1 hmn
    calc
      erdosWeight n m * rhoDrop n m
          ≤ erdosWeight n m * (3 * (m : ℝ) / Real.sqrt (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hrho hew
      _ = (3 / Real.sqrt (n : ℝ)) * (erdosWeight n m * (m : ℝ)) := by ring
  calc
    (∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m * rhoDrop n m)
        ≤ ∑ m ∈ Finset.Icc (M + 1) (n - 1),
            (3 / Real.sqrt (n : ℝ)) * (erdosWeight n m * (m : ℝ)) :=
          Finset.sum_le_sum hpoint
    _ = (3 / Real.sqrt (n : ℝ)) *
          (∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m * (m : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ (3 / Real.sqrt (n : ℝ)) * (K / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hKn (by positivity)
    _ ≤ 3 * (K / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef_le (by positivity)
    _ = (3 * K) / (n : ℝ) := by ring
