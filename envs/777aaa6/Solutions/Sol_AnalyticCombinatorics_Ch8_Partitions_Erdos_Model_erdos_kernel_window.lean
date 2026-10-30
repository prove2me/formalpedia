-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.Model.erdos_kernel_window
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:32:22.114591+00:00
-- url     : https://prove2.me/submissions/4f54ace8-41bd-4b18-956d-7cda1ce951a2

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ModelAssembly
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Mathlib

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

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

section
/-!
# Uniform window replacements for the Erdős kernel

On the window `m ≤ b√n` the two kernel ingredients admit uniform `O(1/√n)`-quality replacements:

* `√n − √(n−m) = m/(√n + √(n−m))` (exact rationalization), with
  `|(√n − √(n−m)) − m/(2√n)| ≤ b²/(2√n)`;
* `|1/(n−m) − 1/n| ≤ 2b/n^{3/2}` (for `2m ≤ n`).

These are the estimates that convert `erdosWeight` into the model kernel
`(σ(m)/n)·e^{−(C/2)m/√n}` uniformly on fixed windows.  Opus-authored during the codex outage.
-/

noncomputable section

open Real

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Exact rationalization: `√n − √(n−m) = m/(√n + √(n−m))` for `m ≤ n`, `1 ≤ n`. -/
lemma sqrt_diff_eq {n m : ℕ} (hm : m ≤ n) (hn : 1 ≤ n) :
    Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ)
      = (m : ℝ) / (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) := by
  have hnm : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by
    push_cast [Nat.cast_sub hm]; ring
  have hs : (0 : ℝ) < Real.sqrt n := by
    apply Real.sqrt_pos.mpr; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hden : (0 : ℝ) < Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ) := by
    have := Real.sqrt_nonneg ((n - m : ℕ) : ℝ); linarith
  rw [eq_div_iff hden.ne']
  have hsq1 : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hsq2 : Real.sqrt ((n - m : ℕ) : ℝ) * Real.sqrt ((n - m : ℕ) : ℝ)
      = ((n - m : ℕ) : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have expand :
      (Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ))
        * (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ))
      = (n : ℝ) - ((n - m : ℕ) : ℝ) := by
    have : (Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ))
        * (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ))
        = Real.sqrt n * Real.sqrt n
          - Real.sqrt ((n - m : ℕ) : ℝ) * Real.sqrt ((n - m : ℕ) : ℝ) := by ring
    rw [this, hsq1, hsq2]
  rw [expand, hnm]; ring

/-- Uniform second-order bound on the window: `|(√n − √(n−m)) − m/(2√n)| ≤ b²/(2√n)`
for `m ≤ b√n`, `m ≤ n`, `1 ≤ n`. -/
lemma sqrt_diff_window_approx {b : ℝ} {n m : ℕ} (_hb : 0 ≤ b)
    (hm : m ≤ n) (hn : 1 ≤ n) (hwin : (m : ℝ) ≤ b * Real.sqrt n) :
    |(Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ)) - (m : ℝ) / (2 * Real.sqrt n)|
      ≤ b ^ 2 / (2 * Real.sqrt n) := by
  have hs : (0 : ℝ) < Real.sqrt n := by
    apply Real.sqrt_pos.mpr; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hs2 : (0 : ℝ) ≤ Real.sqrt ((n - m : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hden : (0 : ℝ) < Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ) := by linarith
  rw [sqrt_diff_eq hm hn]
  -- m/(√n+√(n−m)) − m/(2√n) = m·(2√n − (√n+√(n−m)))/((√n+√(n−m))·2√n)
  --                        = m·(√n − √(n−m))/((√n+√(n−m))·2√n)
  --                        = m²/((√n+√(n−m))²·2√n)
  have key :
      (m : ℝ) / (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) - (m : ℝ) / (2 * Real.sqrt n)
        = (m : ℝ) * (Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ))
          / ((Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) * (2 * Real.sqrt n)) := by
    field_simp
    ring
  rw [key, sqrt_diff_eq hm hn]
  -- now the expression is m·(m/(√n+√(n−m))) / ((√n+√(n−m))·2√n) = m²/((√n+√(n−m))²·2√n)
  have hnonneg : (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) / (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)))
      / ((Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) * (2 * Real.sqrt n)) := by positivity
  rw [abs_of_nonneg hnonneg]
  -- bound: denominator (√n+√(n−m))² ≥ n; numerator m² ≤ b²n
  have hm2 : (m : ℝ) ^ 2 ≤ b ^ 2 * (n : ℝ) := by
    have h1 : (m : ℝ) ^ 2 ≤ (b * Real.sqrt n) ^ 2 := by
      apply sq_le_sq' _ hwin
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith [mul_nonneg _hb hs.le]
    calc (m : ℝ) ^ 2 ≤ (b * Real.sqrt n) ^ 2 := h1
      _ = b ^ 2 * (Real.sqrt n * Real.sqrt n) := by ring
      _ = b ^ 2 * (n : ℝ) := by rw [Real.mul_self_sqrt (Nat.cast_nonneg n)]
  have hdensq : (n : ℝ) ≤ (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) ^ 2 := by
    have h1 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    nlinarith [hs.le, hs2]
  -- assemble
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  calc (m : ℝ) * ((m : ℝ) / (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)))
        / ((Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) * (2 * Real.sqrt n))
      = (m : ℝ) ^ 2 / ((Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) ^ 2 * (2 * Real.sqrt n)) := by
        field_simp
    _ ≤ b ^ 2 * (n : ℝ) / ((n : ℝ) * (2 * Real.sqrt n)) := by
        exact div_le_div₀ (by positivity) hm2 (by positivity)
          (mul_le_mul_of_nonneg_right hdensq (by positivity))
    _ = b ^ 2 / (2 * Real.sqrt n) := by
        field_simp

/-- Uniform reciprocal replacement: `|1/(n−m) − 1/n| ≤ 2b/n^{3/2}` for `m ≤ b√n`, `2m ≤ n`, `1 ≤ n`. -/
lemma inv_window_approx {b : ℝ} {n m : ℕ} (hb : 0 ≤ b)
    (h2 : 2 * m ≤ n) (hn : 1 ≤ n) (hwin : (m : ℝ) ≤ b * Real.sqrt n) :
    |1 / (((n - m : ℕ) : ℝ)) - 1 / (n : ℝ)|
      ≤ 2 * b / ((n : ℝ) * Real.sqrt n) := by
  have hm : m ≤ n := le_trans (Nat.le_mul_of_pos_left m (by norm_num)) h2
  have hnm : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by
    push_cast [Nat.cast_sub hm]; ring
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hhalf : (n : ℝ) / 2 ≤ ((n - m : ℕ) : ℝ) := by
    rw [hnm]
    have : (2 * m : ℕ) ≤ n := h2
    have h2' : 2 * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  have hnmpos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := lt_of_lt_of_le (by linarith) hhalf
  have hdiff : 1 / (((n - m : ℕ) : ℝ)) - 1 / (n : ℝ)
      = (m : ℝ) / (((n - m : ℕ) : ℝ) * (n : ℝ)) := by
    have hne1 : ((n - m : ℕ) : ℝ) ≠ 0 := hnmpos.ne'
    have hne2 : (n : ℝ) ≠ 0 := hnpos.ne'
    rw [div_sub_div _ _ hne1 hne2]
    congr 1
    rw [hnm]; ring
  rw [hdiff]
  have hnonneg : (0 : ℝ) ≤ (m : ℝ) / (((n - m : ℕ) : ℝ) * (n : ℝ)) := by positivity
  rw [abs_of_nonneg hnonneg]
  -- m/((n−m)·n) ≤ (b√n)/((n/2)·n) = 2b√n/n² = 2b/(n^{3/2})
  have hbound : (m : ℝ) / (((n - m : ℕ) : ℝ) * (n : ℝ))
      ≤ (b * Real.sqrt n) / (((n : ℝ) / 2) * (n : ℝ)) := by
    exact div_le_div₀ (by positivity) hwin (by positivity)
      (mul_le_mul_of_nonneg_right hhalf hnpos.le)
  refine hbound.trans ?_
  have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have heq : b * Real.sqrt n * ((n : ℝ) * Real.sqrt n)
      = 2 * b * ((n : ℝ) / 2 * (n : ℝ)) := by
    calc b * Real.sqrt n * ((n : ℝ) * Real.sqrt n)
        = b * (n : ℝ) * (Real.sqrt n * Real.sqrt n) := by ring
      _ = b * (n : ℝ) * (n : ℝ) := by rw [hsq]
      _ = 2 * b * ((n : ℝ) / 2 * (n : ℝ)) := by ring
  exact le_of_eq heq

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Window differences of the divisor summatory function

From the banked `sigma_summatory_asymptotic` (`Σ_{m≤x} σ₁(m) = π²x²/12 + O(x log x)` with an
explicit constant), the difference of the summatory over a window `(α√n, β√n]` is
`(π²/12)·n·(β²−α²) + O(√n·log n)` — the estimate the Erdős kernel window limit consumes.

Opus-authored during the codex quota outage (Jun 5–10).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

/-- Convenience: the summatory function `S(x) = Σ_{m ∈ Icc 1 ⌊x⌋} σR m`. -/
noncomputable def summatory (x : ℝ) : ℝ := ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, sigmaR m

/-- The summatory window difference: for `1 ≤ α√n < β√n`,
`|S(β√n) − S(α√n) − (π²/12)n(β²−α²)| ≤ K·(α+β)·√n·log(2β√n)` with the explicit `K` from
`sigma_summatory_asymptotic`. -/
theorem summatory_window_diff :
    ∃ K, 0 < K ∧ ∀ α β : ℝ, ∀ n : ℕ, 0 ≤ α → α < β →
      1 ≤ α * Real.sqrt n →
      |summatory (β * Real.sqrt n) - summatory (α * Real.sqrt n)
          - (Real.pi ^ 2 / 12) * (n : ℝ) * (β ^ 2 - α ^ 2)|
        ≤ K * (α + β) * Real.sqrt n * Real.log (2 * (β * Real.sqrt n)) := by
  obtain ⟨K, hK, hbound⟩ := sigma_summatory_asymptotic
  refine ⟨K, hK, ?_⟩
  intro α β n hα hαβ hα1
  have hsq : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hβ1 : 1 ≤ β * Real.sqrt n := le_trans hα1 (by
    have : α * Real.sqrt n ≤ β * Real.sqrt n :=
      mul_le_mul_of_nonneg_right hαβ.le hsq
    linarith)
  have hβpos : 0 < β := lt_of_le_of_lt hα hαβ
  -- the two endpoint estimates
  have hA := hbound (α * Real.sqrt n) hα1
  have hB := hbound (β * Real.sqrt n) hβ1
  -- (α√n)² = α²·n  and  (β√n)² = β²·n
  have hsqn : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hA2 : (α * Real.sqrt n) ^ 2 = α ^ 2 * (n : ℝ) := by
    rw [mul_pow, sq, sq, hsqn]
  have hB2 : (β * Real.sqrt n) ^ 2 = β ^ 2 * (n : ℝ) := by
    rw [mul_pow, sq, sq, hsqn]
  -- main term difference matches
  have hmain :
      (Real.pi ^ 2 / 12) * (β * Real.sqrt n) ^ 2
        - (Real.pi ^ 2 / 12) * (α * Real.sqrt n) ^ 2
        = (Real.pi ^ 2 / 12) * (n : ℝ) * (β ^ 2 - α ^ 2) := by
    rw [hA2, hB2]; ring
  -- log monotonicity: log(2α√n) ≤ log(2β√n)
  have hlogmono : Real.log (2 * (α * Real.sqrt n)) ≤ Real.log (2 * (β * Real.sqrt n)) := by
    apply Real.log_le_log (by linarith)
    have : α * Real.sqrt n ≤ β * Real.sqrt n :=
      mul_le_mul_of_nonneg_right hαβ.le hsq
    linarith
  -- assemble: |S(β√n)−S(α√n) − main| ≤ |S(β√n)−π²(β√n)²/12| + |S(α√n)−π²(α√n)²/12|
  have key :
      |summatory (β * Real.sqrt n) - summatory (α * Real.sqrt n)
          - (Real.pi ^ 2 / 12) * (n : ℝ) * (β ^ 2 - α ^ 2)|
        ≤ K * (β * Real.sqrt n) * Real.log (2 * (β * Real.sqrt n))
          + K * (α * Real.sqrt n) * Real.log (2 * (α * Real.sqrt n)) := by
    have expand :
        summatory (β * Real.sqrt n) - summatory (α * Real.sqrt n)
            - (Real.pi ^ 2 / 12) * (n : ℝ) * (β ^ 2 - α ^ 2)
          = (summatory (β * Real.sqrt n) - (Real.pi ^ 2 / 12) * (β * Real.sqrt n) ^ 2)
            - (summatory (α * Real.sqrt n) - (Real.pi ^ 2 / 12) * (α * Real.sqrt n) ^ 2) := by
      rw [← hmain]; ring
    rw [expand]
    calc |(summatory (β * Real.sqrt n) - (Real.pi ^ 2 / 12) * (β * Real.sqrt n) ^ 2)
          - (summatory (α * Real.sqrt n) - (Real.pi ^ 2 / 12) * (α * Real.sqrt n) ^ 2)|
        ≤ |summatory (β * Real.sqrt n) - (Real.pi ^ 2 / 12) * (β * Real.sqrt n) ^ 2|
          + |summatory (α * Real.sqrt n) - (Real.pi ^ 2 / 12) * (α * Real.sqrt n) ^ 2| :=
          abs_sub _ _
      _ ≤ K * (β * Real.sqrt n) * Real.log (2 * (β * Real.sqrt n))
          + K * (α * Real.sqrt n) * Real.log (2 * (α * Real.sqrt n)) := by
          exact add_le_add hB hA
  -- final absorption: K·β√n·log(2β√n) + K·α√n·log(2α√n) ≤ K(α+β)√n·log(2β√n)
  refine key.trans ?_
  have hlogβpos : 0 ≤ Real.log (2 * (β * Real.sqrt n)) := by
    apply Real.log_nonneg; linarith
  have h2 : K * (α * Real.sqrt n) * Real.log (2 * (α * Real.sqrt n))
      ≤ K * (α * Real.sqrt n) * Real.log (2 * (β * Real.sqrt n)) := by
    apply mul_le_mul_of_nonneg_left hlogmono
    positivity
  calc K * (β * Real.sqrt n) * Real.log (2 * (β * Real.sqrt n))
        + K * (α * Real.sqrt n) * Real.log (2 * (α * Real.sqrt n))
      ≤ K * (β * Real.sqrt n) * Real.log (2 * (β * Real.sqrt n))
        + K * (α * Real.sqrt n) * Real.log (2 * (β * Real.sqrt n)) := by linarith
    _ = K * (α + β) * Real.sqrt n * Real.log (2 * (β * Real.sqrt n)) := by ring

end AnalyticCombinatorics.Ch8.Partitions.Sigma
end
end

section
/-!
# Model-kernel window limit for the Erdős partition route

This file isolates the model-kernel window limit

  (1/n) * Σ_{1 ≤ m ≤ n-1, a√n ≤ m ≤ b√n}
    σ(m) * exp (-(C/2) * m / √n)
  →
  ∫ y in a..b, (π²/6) * y * exp (-(C/2)y)

The proof is deliberately split into:

1. basic summatory-window mass convergence for half-open windows;
2. a first-window `α = 0` variant using `sigma_summatory_asymptotic`;
3. the final real-variable step approximation theorem.

The final step approximation theorem is marked as the only remaining prover task.
It is the sub-block squeeze/Riemann-Stieltjes argument described in the prompt.
-/

-- generous heartbeats: long ε-bookkeeping chains in the windowed summatory limits
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

noncomputable section

open Filter Finset
open scoped BigOperators Topology Interval

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

local notation "σR" => Sigma.sigmaR
local notation "Sσ" => Sigma.summatory

/-- Main quadratic constant for the summatory divisor function. -/
noncomputable def Q : ℝ := Real.pi ^ 2 / 12

/-- Half-open unweighted mass `(α√n, β√n]`, scaled by `1/n`. -/
noncomputable def halfOpenMass (α β : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) *
    (Sσ (β * Real.sqrt (n : ℝ)) - Sσ (α * Real.sqrt (n : ℝ)))

private lemma sqrt_nat_atTop :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

private lemma sqrt_nat_pos_eventually :
    ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (n : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact Real.sqrt_pos_of_pos (by exact_mod_cast hn)

private lemma log_const_mul_sqrt_over_sqrt_tendsto_zero
    {β : ℝ} (hβ : 0 < β) :
    Tendsto
      (fun n : ℕ =>
        Real.log (2 * (β * Real.sqrt (n : ℝ))) /
          Real.sqrt (n : ℝ))
      atTop
      (𝓝 0) := by
  have hsqrt := sqrt_nat_atTop
  have hreal :
      Tendsto
        (fun x : ℝ => Real.log (2 * (β * x)) / x)
        atTop
        (𝓝 0) := by
    have hmulpos : 0 < 2 * β := by positivity
    have h1 :
        Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h2 :
        Tendsto (fun x : ℝ => Real.log (2 * β) / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hsum := h1.add h2
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [show (2 : ℝ) * (β * x) = (2 * β) * x by ring,
      Real.log_mul hmulpos.ne' hx.ne']
    ring
  exact hreal.comp hsqrt

private lemma alpha_sqrt_ge_one_eventually
    {α : ℝ} (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ α * Real.sqrt (n : ℝ) := by
  have ht :
      Tendsto (fun n : ℕ => α * Real.sqrt (n : ℝ)) atTop atTop := by
    exact (sqrt_nat_atTop.const_mul_atTop hα)
  exact ht.eventually_ge_atTop 1

/--
First-window summatory mass, i.e. the case `α = 0`:

`S(β√n)/n → Q β²`.
-/
lemma summatory_zero_to_beta_scaled_tendsto
    {β : ℝ} (hβ : 0 < β) :
    Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * Sσ (β * Real.sqrt (n : ℝ)))
      atTop
      (𝓝 (Q * β ^ 2)) := by
  rcases Sigma.sigma_summatory_asymptotic with ⟨K, hKpos, hK⟩
  have hmain :
      Tendsto
        (fun n : ℕ =>
          (1 / (n : ℝ)) *
            (Q * (β * Real.sqrt (n : ℝ)) ^ 2))
        atTop
        (𝓝 (Q * β ^ 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnz : (n : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : n ≠ 0)
    have hsqr :
        (β * Real.sqrt (n : ℝ)) ^ 2 = β ^ 2 * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
    rw [hsqr]
    field_simp [hnz]
  have herr :
      Tendsto
        (fun n : ℕ =>
          (1 / (n : ℝ)) *
            (Sσ (β * Real.sqrt (n : ℝ)) -
              Q * (β * Real.sqrt (n : ℝ)) ^ 2))
        atTop
        (𝓝 0) := by
    refine squeeze_zero_norm'
      (a := fun n : ℕ => K * β *
        (Real.log (2 * (β * Real.sqrt (n : ℝ))) / Real.sqrt (n : ℝ))) ?_ ?_
    · filter_upwards
        [eventually_ge_atTop (1 : ℕ),
         ((sqrt_nat_atTop.const_mul_atTop hβ)).eventually_ge_atTop 1]
        with n hn hx
      rw [Real.norm_eq_abs]
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
      have hspos : 0 < Real.sqrt (n : ℝ) :=
        Real.sqrt_pos_of_pos (by exact_mod_cast hn)
      have hbound := hK (β * Real.sqrt (n : ℝ)) hx
      have hrewrite :
          (1 / (n : ℝ)) *
              (K * (β * Real.sqrt (n : ℝ)) *
                Real.log (2 * (β * Real.sqrt (n : ℝ))))
            =
          K * β *
            (Real.log (2 * (β * Real.sqrt (n : ℝ))) /
              Real.sqrt (n : ℝ)) := by
        have hsqr :
            Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
          Real.mul_self_sqrt (by positivity : 0 ≤ (n : ℝ))
        field_simp [hnpos.ne', hspos.ne', hsqr]
        rw [sq, hsqr]
      calc
        |(1 / (n : ℝ)) *
            (Sσ (β * Real.sqrt (n : ℝ)) -
              Q * (β * Real.sqrt (n : ℝ)) ^ 2)|
            =
          (1 / (n : ℝ)) *
            |Sσ (β * Real.sqrt (n : ℝ)) -
              Q * (β * Real.sqrt (n : ℝ)) ^ 2| := by
              rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / (n : ℝ))]
        _ ≤
          (1 / (n : ℝ)) *
            (K * (β * Real.sqrt (n : ℝ)) *
              Real.log (2 * (β * Real.sqrt (n : ℝ)))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              dsimp [Q]
              simpa using hbound
        _ =
          K * β *
            (Real.log (2 * (β * Real.sqrt (n : ℝ))) /
              Real.sqrt (n : ℝ)) := hrewrite
    · have ht :=
        log_const_mul_sqrt_over_sqrt_tendsto_zero (β := β) hβ
      simpa [mul_assoc] using
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => K * β) atTop (𝓝 (K * β))).mul ht)
  have hsum := herr.add hmain
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards with n
  ring

/--
Half-open window mass convergence:

`(S(β√n)-S(α√n))/n → Q(β²-α²)`.
-/
lemma halfOpenMass_tendsto
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α < β) :
    Tendsto (halfOpenMass α β) atTop
      (𝓝 (Q * (β ^ 2 - α ^ 2))) := by
  by_cases hαzero : α = 0
  · subst hαzero
    have hβ : 0 < β := lt_of_le_of_lt hα hαβ
    have hfirst := summatory_zero_to_beta_scaled_tendsto (β := β) hβ
    have hfun : halfOpenMass 0 β = fun n : ℕ =>
        (1 / (n : ℝ)) * Sσ (β * Real.sqrt (n : ℝ)) := by
      funext n
      have hS0 : Sσ ((0 : ℝ) * Real.sqrt (n : ℝ)) = 0 := by
        have : ((0 : ℝ) * Real.sqrt (n : ℝ)) = 0 := by ring
        rw [this]
        unfold Sigma.summatory
        rw [show ⌊(0 : ℝ)⌋₊ = 0 from Nat.floor_zero]
        rw [Finset.Icc_eq_empty (by norm_num : ¬(1 : ℕ) ≤ 0)]
        exact Finset.sum_empty
      unfold halfOpenMass
      rw [hS0, sub_zero]
    rw [hfun]
    simpa [Q] using hfirst
  · have hαpos : 0 < α := lt_of_le_of_ne' hα hαzero
    rcases Sigma.summatory_window_diff with ⟨K, hKpos, hK⟩
    have herr :
        Tendsto
          (fun n : ℕ =>
            (1 / (n : ℝ)) *
              ((Sσ (β * Real.sqrt (n : ℝ)) -
                  Sσ (α * Real.sqrt (n : ℝ))) -
                Q * (n : ℝ) * (β ^ 2 - α ^ 2)))
          atTop
          (𝓝 0) := by
      refine squeeze_zero_norm'
        (a := fun n : ℕ => K * (α + β) *
          (Real.log (2 * (β * Real.sqrt (n : ℝ))) / Real.sqrt (n : ℝ))) ?_ ?_
      · filter_upwards
          [eventually_ge_atTop (1 : ℕ),
           alpha_sqrt_ge_one_eventually (α := α) hαpos]
          with n hn hα1
        rw [Real.norm_eq_abs]
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
        have hbound := hK α β n hα hαβ hα1
        calc
          |(1 / (n : ℝ)) *
            ((Sσ (β * Real.sqrt (n : ℝ)) -
                Sσ (α * Real.sqrt (n : ℝ))) -
              Q * (n : ℝ) * (β ^ 2 - α ^ 2))|
              =
            (1 / (n : ℝ)) *
              |(Sσ (β * Real.sqrt (n : ℝ)) -
                  Sσ (α * Real.sqrt (n : ℝ))) -
                Q * (n : ℝ) * (β ^ 2 - α ^ 2)| := by
                rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / (n : ℝ))]
          _ ≤
            (1 / (n : ℝ)) *
              (K * (α + β) * Real.sqrt (n : ℝ) *
                Real.log (2 * (β * Real.sqrt (n : ℝ)))) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                dsimp [Q]
                simpa using hbound
          _ =
            K * (α + β) *
              (Real.log (2 * (β * Real.sqrt (n : ℝ))) /
                Real.sqrt (n : ℝ)) := by
                have hspos : 0 < Real.sqrt (n : ℝ) :=
                  Real.sqrt_pos_of_pos (by exact_mod_cast hn)
                have hsqr :
                    Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
                  Real.mul_self_sqrt (by positivity : 0 ≤ (n : ℝ))
                field_simp [hnpos.ne', hspos.ne', hsqr]
                rw [sq, hsqr]
                ring
      · have hβpos : 0 < β := lt_trans hαpos hαβ
        have ht :=
          log_const_mul_sqrt_over_sqrt_tendsto_zero (β := β) hβpos
        simpa [mul_assoc] using
          ((tendsto_const_nhds :
            Tendsto (fun _ : ℕ => K * (α + β))
              atTop
              (𝓝 (K * (α + β)))).mul ht)
    have hmain :
        Tendsto
          (fun n : ℕ =>
            (1 / (n : ℝ)) *
              (Q * (n : ℝ) * (β ^ 2 - α ^ 2)))
          atTop
          (𝓝 (Q * (β ^ 2 - α ^ 2))) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hnz : (n : ℝ) ≠ 0 := by
        exact_mod_cast (by omega : n ≠ 0)
      field_simp [hnz]
    have hsum := herr.add hmain
    rw [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards with n
    dsimp [halfOpenMass]
    ring

/--
For fixed `α < β`, the exponential factor is squeezed between endpoint values
on the block `(α√n, β√n]`.
-/
lemma model_exp_endpoint_squeeze
    {C α β : ℝ} (hC : 0 < C) (_hαβ : α ≤ β) :
    ∀ᶠ n : ℕ in atTop,
      ∀ m : ℕ,
        α * Real.sqrt (n : ℝ) < (m : ℝ) →
        (m : ℝ) ≤ β * Real.sqrt (n : ℝ) →
          Real.exp (-(C / 2) * β)
            ≤ Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) ∧
          Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ))
            ≤ Real.exp (-(C / 2) * α) := by
  filter_upwards [sqrt_nat_pos_eventually] with n hspos m hmα hmβ
  have hdiv_lower : α ≤ (m : ℝ) / Real.sqrt (n : ℝ) := by
    exact (le_div_iff₀ hspos).mpr hmα.le
  have hdiv_upper : (m : ℝ) / Real.sqrt (n : ℝ) ≤ β := by
    exact (div_le_iff₀ hspos).mpr hmβ
  constructor
  · apply Real.exp_le_exp.mpr
    have hlam : 0 ≤ C / 2 := by linarith
    have hform : -(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)
        = -(C / 2 * ((m : ℝ) / Real.sqrt (n : ℝ))) := by ring
    rw [hform]
    have hmul := mul_le_mul_of_nonneg_left hdiv_upper hlam
    linarith
  · apply Real.exp_le_exp.mpr
    have hlam : 0 ≤ C / 2 := by linarith
    have hform : -(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)
        = -(C / 2 * ((m : ℝ) / Real.sqrt (n : ℝ))) := by ring
    rw [hform]
    have hmul := mul_le_mul_of_nonneg_left hdiv_lower hlam
    linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos.Model
end
end

section
/-!
# The summatory ↔ windowed-sum index bridge

`S(β√n) − S(α√n) = Σ_{m ∈ Icc 1 (n−1)} [α√n < m ≤ β√n]·σ(m)` whenever `β√n ≤ n−1` — the
identity that converts half-open summatory masses into the if-windowed sums used by the
Erdős model kernel.  Opus-authored during the codex outage.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

/-- `Ioc` of floors = the real-window filter on `Icc 1 (n-1)`. -/
lemma window_filter_eq_Ioc {α β : ℝ} (hα : 0 ≤ α) {n : ℕ}
    (hcap : ⌊β * Real.sqrt n⌋₊ ≤ n - 1) :
    (Finset.Icc 1 (n - 1)).filter
        (fun m : ℕ => α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n)
      = Finset.Ioc ⌊α * Real.sqrt n⌋₊ ⌊β * Real.sqrt n⌋₊ := by
  have hαs : 0 ≤ α * Real.sqrt n := mul_nonneg hα (Real.sqrt_nonneg _)
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_, _⟩, hlt, hle⟩
    exact ⟨(Nat.floor_lt hαs).mpr hlt, Nat.le_floor hle⟩
  · rintro ⟨hlt, hle⟩
    have h1 : α * Real.sqrt n < (m : ℝ) := (Nat.floor_lt hαs).mp hlt
    have hm1 : 1 ≤ m := by omega
    have hb1 : 1 ≤ ⌊β * Real.sqrt n⌋₊ := le_trans hm1 hle
    have hβs : 0 ≤ β * Real.sqrt n := by
      by_contra hneg
      have h0 : ⌊β * Real.sqrt n⌋₊ = 0 :=
        Nat.floor_of_nonpos (le_of_lt (not_le.mp hneg))
      omega
    have h2 : (m : ℝ) ≤ β * Real.sqrt n := by
      calc (m : ℝ) ≤ (⌊β * Real.sqrt n⌋₊ : ℝ) := by exact_mod_cast hle
        _ ≤ β * Real.sqrt n := Nat.floor_le hβs
    exact ⟨⟨hm1, le_trans hle hcap⟩, h1, h2⟩

/-- **The index bridge**: for `0 ≤ α ≤ β` and `⌊β√n⌋ ≤ n−1`,
`S(β√n) − S(α√n) = Σ_{m ∈ Icc 1 (n−1)} [α√n < m ≤ β√n]·σ(m)`. -/
theorem summatory_diff_eq_window_sum {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) {n : ℕ}
    (hcap : ⌊β * Real.sqrt n⌋₊ ≤ n - 1) :
    summatory (β * Real.sqrt n) - summatory (α * Real.sqrt n)
      = ∑ m ∈ Finset.Icc 1 (n - 1),
          (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
           then sigmaR m else 0) := by
  set a := ⌊α * Real.sqrt n⌋₊ with ha_def
  set b := ⌊β * Real.sqrt n⌋₊ with hb_def
  have hab : a ≤ b := by
    apply Nat.floor_le_floor
    exact mul_le_mul_of_nonneg_right hαβ (Real.sqrt_nonneg _)
  -- RHS = sum over the Ioc of floors
  have hrhs :
      (∑ m ∈ Finset.Icc 1 (n - 1),
          (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
           then sigmaR m else 0))
        = ∑ m ∈ Finset.Ioc a b, sigmaR m := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [window_filter_eq_Ioc hα hcap]
  rw [hrhs]
  -- LHS: summatory difference = sum over Ioc a b
  unfold summatory
  rw [← hb_def, ← ha_def]
  have hIcc_Ioc : ∀ k : ℕ, Finset.Icc 1 k = Finset.Ioc 0 k := by
    intro k
    ext m
    simp [Finset.mem_Icc, Finset.mem_Ioc, Nat.lt_iff_add_one_le]
  have hsplit :
      (∑ m ∈ Finset.Ioc 0 a, sigmaR m) + ∑ m ∈ Finset.Ioc a b, sigmaR m
        = ∑ m ∈ Finset.Ioc 0 b, sigmaR m :=
    Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab
  rw [hIcc_Ioc b, hIcc_Ioc a, ← hsplit]
  ring

end AnalyticCombinatorics.Ch8.Partitions.Sigma
end
end

section
/-!
# The weighted block squeeze (rehabilitated)

With the index bridge in hand, the model-kernel windowed sum is squeezed between the endpoint
exponentials times the *same* half-open mass — both sides living on `Icc 1 (n−1)`:

  `e^{−(C/2)β}·M_n(α,β) ≤ (1/n)·Σ_{window} σ(m)·e^{−(C/2)m/√n} ≤ e^{−(C/2)α}·M_n(α,β)`,

eventually in `n`, where `M_n(α,β) = (S(β√n) − S(α√n))/n`.  Opus-authored.
-/

noncomputable section

open Filter Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

open AnalyticCombinatorics.Ch8.Partitions.Sigma

/-- Eventually `⌊β√n⌋ ≤ n − 1`. -/
lemma floor_beta_sqrt_le_eventually {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ n : ℕ in atTop, ⌊β * Real.sqrt n⌋₊ ≤ n - 1 := by
  have hquad : ∀ᶠ n : ℕ in atTop, (4 * β ^ 2 ≤ (n : ℝ)) ∧ 2 ≤ n := by
    have h1 : ∀ᶠ n : ℕ in atTop, ((⌈4 * β ^ 2⌉₊ : ℕ) ≤ n) := eventually_ge_atTop _
    have h2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
    filter_upwards [h1, h2] with n hn h2n
    refine ⟨?_, h2n⟩
    calc (4 * β ^ 2 : ℝ) ≤ (⌈4 * β ^ 2⌉₊ : ℕ) := Nat.le_ceil _
      _ ≤ (n : ℝ) := by exact_mod_cast hn
  filter_upwards [hquad] with n ⟨hn4, hn2⟩
  -- β√n ≤ n/2 ≤ n−1 for n ≥ 2
  have hnpos : (0 : ℝ) < n := by positivity
  have hs : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hsqrtle : 2 * β ≤ Real.sqrt n := by
    have h2β : (0 : ℝ) ≤ 2 * β := by positivity
    have : (2 * β) ^ 2 ≤ (n : ℝ) := by nlinarith
    calc 2 * β = Real.sqrt ((2 * β) ^ 2) := (Real.sqrt_sq h2β).symm
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt this
  have hhalf : β * Real.sqrt n ≤ (n : ℝ) / 2 := by
    have hs0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    nlinarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
  have hfin : β * Real.sqrt n ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [hcast]
    have h2n' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  calc ⌊β * Real.sqrt n⌋₊ ≤ ⌊((n - 1 : ℕ) : ℝ)⌋₊ := Nat.floor_le_floor hfin
    _ = n - 1 := Nat.floor_natCast _

/-- **The weighted block squeeze**: eventually in `n`, the model-kernel windowed sum lies between
the endpoint exponentials times the half-open mass. -/
theorem weighted_window_block_squeeze {C α β : ℝ} (hC : 0 < C) (hα : 0 ≤ α) (hαβ : α < β) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-(C / 2) * β) *
          ((1 / (n : ℝ)) * (summatory (β * Real.sqrt n) - summatory (α * Real.sqrt n)))
        ≤ (1 / (n : ℝ)) *
            ∑ m ∈ Finset.Icc 1 (n - 1),
              (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
               then sigmaR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt n) else 0)
      ∧ (1 / (n : ℝ)) *
            ∑ m ∈ Finset.Icc 1 (n - 1),
              (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
               then sigmaR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt n) else 0)
        ≤ Real.exp (-(C / 2) * α) *
            ((1 / (n : ℝ)) * (summatory (β * Real.sqrt n) - summatory (α * Real.sqrt n))) := by
  have hβ : 0 < β := lt_of_le_of_lt hα hαβ
  filter_upwards
    [floor_beta_sqrt_le_eventually hβ,
     model_exp_endpoint_squeeze (C := C) (α := α) (β := β) hC hαβ.le]
    with n hcap hsq
  have hbridge := summatory_diff_eq_window_sum hα hαβ.le (n := n) hcap
  have hcoef : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  constructor
  · -- lower: e^{−(C/2)β}·mass ≤ windowed sum
    rw [hbridge]
    rw [show Real.exp (-(C / 2) * β) *
          ((1 / (n : ℝ)) * ∑ m ∈ Finset.Icc 1 (n - 1),
            (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
             then sigmaR m else 0))
        = (1 / (n : ℝ)) * ∑ m ∈ Finset.Icc 1 (n - 1),
            Real.exp (-(C / 2) * β) *
              (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
               then sigmaR m else 0) by
          rw [← Finset.mul_sum]; ring]
    refine mul_le_mul_of_nonneg_left ?_ hcoef
    refine Finset.sum_le_sum ?_
    intro m _hm
    by_cases hwin : α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
    · simp only [hwin]
      have hσ : 0 ≤ sigmaR m := sigmaR_nonneg m
      have hexp := (hsq m hwin.1 hwin.2).1
      calc Real.exp (-(C / 2) * β) * sigmaR m
          ≤ Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt n) * sigmaR m :=
            mul_le_mul_of_nonneg_right hexp hσ
        _ = sigmaR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt n) := by ring
    · simp [hwin]
  · -- upper: windowed sum ≤ e^{−(C/2)α}·mass
    rw [hbridge]
    rw [show Real.exp (-(C / 2) * α) *
          ((1 / (n : ℝ)) * ∑ m ∈ Finset.Icc 1 (n - 1),
            (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
             then sigmaR m else 0))
        = (1 / (n : ℝ)) * ∑ m ∈ Finset.Icc 1 (n - 1),
            Real.exp (-(C / 2) * α) *
              (if α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
               then sigmaR m else 0) by
          rw [← Finset.mul_sum]; ring]
    refine mul_le_mul_of_nonneg_left ?_ hcoef
    refine Finset.sum_le_sum ?_
    intro m _hm
    by_cases hwin : α * Real.sqrt n < (m : ℝ) ∧ (m : ℝ) ≤ β * Real.sqrt n
    · simp only [hwin]
      have hσ : 0 ≤ sigmaR m := sigmaR_nonneg m
      have hexp := (hsq m hwin.1 hwin.2).2
      calc sigmaR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt n)
          = Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt n) * sigmaR m := by ring
        _ ≤ Real.exp (-(C / 2) * α) * sigmaR m :=
            mul_le_mul_of_nonneg_right hexp hσ
    · simp [hwin]

end AnalyticCombinatorics.Ch8.Partitions.Erdos.Model
end
end

section
/-!
# Mesh assembly for the model-kernel window limit

This file assembles the banked block squeeze and half-open mass limit over a uniform
arithmetic mesh: the half-open block `(a√n, b√n]` partitions into `N` mesh blocks, each
block is squeezed by endpoint exponentials times its half-open mass, and as `n → ∞` the
mesh sums converge to the Stieltjes endpoint sums `lowerMesh`/`upperMesh`.

Main result: `blockSum_eventually_between_mesh_eps` — for any fixed mesh and `ε > 0`,
eventually `lowerMesh − ε ≤ blockSum n ≤ upperMesh + ε`.

The remaining real-variable step (mesh sums → ∫ a..b (π²/6) y e^{−(C/2)y} dy as the mesh
refines) is the next brick; combining the two yields the model-kernel window limit.
ChatGPT-draft + Opus-fix.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology Interval

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

local notation "σR" => Sigma.sigmaR

/-- The weighted half-open model block `(α√n, β√n]`. -/
noncomputable def blockSum (C α β : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) *
    ∑ m ∈ Finset.Icc 1 (n - 1),
      (if α * Real.sqrt (n : ℝ) < (m : ℝ) ∧
          (m : ℝ) ≤ β * Real.sqrt (n : ℝ)
       then σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ))
       else 0)

/-- Uniform arithmetic mesh point `a + k h`. -/
noncomputable def meshPoint (a h : ℝ) (k : ℕ) : ℝ :=
  a + (k : ℝ) * h

/-- Lower Stieltjes endpoint sum on the uniform mesh. -/
noncomputable def lowerMesh (C a h : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    Real.exp (-(C / 2) * meshPoint a h (k + 1)) *
      Q * (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2)

/-- Upper Stieltjes endpoint sum on the uniform mesh. -/
noncomputable def upperMesh (C a h : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    Real.exp (-(C / 2) * meshPoint a h k) *
      Q * (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2)

/-- Lower endpoint mass sequence for one mesh block. -/
noncomputable def lowerSeq (C a h : ℝ) (k n : ℕ) : ℝ :=
  Real.exp (-(C / 2) * meshPoint a h (k + 1)) *
    halfOpenMass (meshPoint a h k) (meshPoint a h (k + 1)) n

/-- Upper endpoint mass sequence for one mesh block. -/
noncomputable def upperSeq (C a h : ℝ) (k n : ℕ) : ℝ :=
  Real.exp (-(C / 2) * meshPoint a h k) *
    halfOpenMass (meshPoint a h k) (meshPoint a h (k + 1)) n

lemma meshPoint_nonneg
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (k : ℕ) :
    0 ≤ meshPoint a h k := by
  dsimp [meshPoint]
  have hk : 0 ≤ (k : ℝ) := by positivity
  nlinarith [mul_nonneg hk hh]

lemma meshPoint_succ_lt
    {a h : ℝ} (hh : 0 < h) (k : ℕ) :
    meshPoint a h k < meshPoint a h (k + 1) := by
  dsimp [meshPoint]
  have hk : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self k
  have := mul_lt_mul_of_pos_right hk hh
  linarith

private lemma blockSum_self (C α : ℝ) (n : ℕ) :
    blockSum C α α n = 0 := by
  classical
  dsimp [blockSum]
  have hsum :
      (∑ m ∈ Finset.Icc 1 (n - 1),
        (if α * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ α * Real.sqrt (n : ℝ)
         then σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ))
         else 0)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro m hm
    have hnot :
        ¬ (α * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ α * Real.sqrt (n : ℝ)) := by
      intro h
      linarith [h.1, h.2]
    rw [if_neg hnot]
  rw [hsum, mul_zero]

/-- Two adjacent half-open windows add exactly. -/
private lemma blockSum_add
    (C a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (n : ℕ) :
    blockSum C a b n =
      blockSum C a c n + blockSum C c b n := by
  classical
  dsimp [blockSum]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  have hs_nonneg : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hacs : a * Real.sqrt (n : ℝ) ≤ c * Real.sqrt (n : ℝ) :=
    mul_le_mul_of_nonneg_right hac hs_nonneg
  have hcbs : c * Real.sqrt (n : ℝ) ≤ b * Real.sqrt (n : ℝ) :=
    mul_le_mul_of_nonneg_right hcb hs_nonneg
  by_cases h1 : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ c * Real.sqrt (n : ℝ)
  · have hab : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ) :=
      ⟨h1.1, le_trans h1.2 hcbs⟩
    have h2 : ¬ (c * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)) := by
      intro h
      exact absurd h1.2 (not_le.mpr h.1)
    rw [if_pos hab, if_pos h1, if_neg h2, add_zero]
  · by_cases h2 : c * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
    · have hab : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ) :=
        ⟨lt_of_le_of_lt hacs h2.1, h2.2⟩
      rw [if_pos hab, if_neg h1, if_pos h2, zero_add]
    · have hab : ¬ (a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)) := by
        intro h
        rcases le_or_gt (m : ℝ) (c * Real.sqrt (n : ℝ)) with hc | hc
        · exact h1 ⟨h.1, hc⟩
        · exact h2 ⟨hc, h.2⟩
      rw [if_neg hab, if_neg h1, if_neg h2, add_zero]

/--
Arithmetic mesh decomposition:

`(a, a + N h]` is the disjoint union of the half-open blocks
`(a + k h, a + (k+1)h]`.
-/
private lemma blockSum_arith_partition
    (C a h : ℝ) (hh : 0 ≤ h) :
    ∀ N n : ℕ,
      blockSum C a (a + (N : ℝ) * h) n =
        ∑ k ∈ Finset.range N,
          blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n := by
  intro N
  induction N with
  | zero =>
      intro n
      simp [meshPoint, blockSum_self]
  | succ N ih =>
      intro n
      have hac : a ≤ a + (N : ℝ) * h := by
        have hmul : 0 ≤ (N : ℝ) * h := by positivity
        linarith
      have hcb :
          a + (N : ℝ) * h ≤ a + ((N + 1 : ℕ) : ℝ) * h := by
        have hk : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ N
        have hmul := mul_le_mul_of_nonneg_right hk hh
        linarith
      calc
        blockSum C a (a + ((N + 1 : ℕ) : ℝ) * h) n
            =
          blockSum C a (a + (N : ℝ) * h) n +
            blockSum C (a + (N : ℝ) * h)
              (a + ((N + 1 : ℕ) : ℝ) * h) n :=
              blockSum_add C a (a + (N : ℝ) * h)
                (a + ((N + 1 : ℕ) : ℝ) * h) hac hcb n
        _ =
          (∑ k ∈ Finset.range N,
            blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n) +
            blockSum C (meshPoint a h N) (meshPoint a h (N + 1)) n := by
              rw [ih n]
              simp [meshPoint]
        _ =
          ∑ k ∈ Finset.range (N + 1),
            blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n := by
              rw [Finset.sum_range_succ]

private lemma lowerSeq_tendsto
    {C a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (k : ℕ) :
    Tendsto
      (fun n : ℕ => lowerSeq C a h k n)
      atTop
      (𝓝
        (Real.exp (-(C / 2) * meshPoint a h (k + 1)) *
          Q * (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2))) := by
  have hα : 0 ≤ meshPoint a h k :=
    meshPoint_nonneg ha hh.le k
  have hαβ : meshPoint a h k < meshPoint a h (k + 1) :=
    meshPoint_succ_lt hh k
  have hm := halfOpenMass_tendsto hα hαβ
  simpa [lowerSeq, mul_assoc] using
    ((tendsto_const_nhds :
      Tendsto
        (fun _ : ℕ => Real.exp (-(C / 2) * meshPoint a h (k + 1)))
        atTop
        (𝓝 (Real.exp (-(C / 2) * meshPoint a h (k + 1))))).mul hm)

private lemma upperSeq_tendsto
    {C a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (k : ℕ) :
    Tendsto
      (fun n : ℕ => upperSeq C a h k n)
      atTop
      (𝓝
        (Real.exp (-(C / 2) * meshPoint a h k) *
          Q * (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2))) := by
  have hα : 0 ≤ meshPoint a h k :=
    meshPoint_nonneg ha hh.le k
  have hαβ : meshPoint a h k < meshPoint a h (k + 1) :=
    meshPoint_succ_lt hh k
  have hm := halfOpenMass_tendsto hα hαβ
  simpa [upperSeq, mul_assoc] using
    ((tendsto_const_nhds :
      Tendsto
        (fun _ : ℕ => Real.exp (-(C / 2) * meshPoint a h k))
        atTop
        (𝓝 (Real.exp (-(C / 2) * meshPoint a h k)))).mul hm)

private lemma weighted_block_squeeze_mesh
    {C a h : ℝ} (hC : 0 < C) (ha : 0 ≤ a) (hh : 0 < h)
    (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      lowerSeq C a h k n
        ≤ blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n ∧
      blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n
        ≤ upperSeq C a h k n := by
  have hα : 0 ≤ meshPoint a h k :=
    meshPoint_nonneg ha hh.le k
  have hαβ : meshPoint a h k < meshPoint a h (k + 1) :=
    meshPoint_succ_lt hh k
  have hs :=
    weighted_window_block_squeeze
      (C := C)
      (α := meshPoint a h k)
      (β := meshPoint a h (k + 1))
      hC hα hαβ
  filter_upwards [hs] with n hn
  simpa [blockSum, lowerSeq, upperSeq, halfOpenMass, mul_assoc] using hn

/--
For a fixed uniform mesh, the full block is eventually squeezed between the
lower and upper mesh sums, with an arbitrary additive tolerance coming only
from the convergence of the block masses.
-/
theorem blockSum_eventually_between_mesh_eps
    {C a b : ℝ} (hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
    {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      lowerMesh C a ((b - a) / (N : ℝ)) N - ε
        ≤ blockSum C a b n ∧
      blockSum C a b n
        ≤ upperMesh C a ((b - a) / (N : ℝ)) N + ε := by
  classical
  set h : ℝ := (b - a) / (N : ℝ) with hdef
  have hNposR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hhpos : 0 < h := by
    rw [hdef]
    exact div_pos (sub_pos.mpr hab) hNposR
  have hhnonneg : 0 ≤ h := hhpos.le
  have hb_eq : b = a + (N : ℝ) * h := by
    rw [hdef]
    field_simp
    ring
  have hlow_tendsto :
      Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range N, lowerSeq C a h k n)
        atTop
        (𝓝 (lowerMesh C a h N)) := by
    dsimp only [lowerMesh]
    exact tendsto_finset_sum (Finset.range N) (by
      intro k _hk
      exact lowerSeq_tendsto (C := C) (a := a) (h := h) ha hhpos k)
  have hup_tendsto :
      Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range N, upperSeq C a h k n)
        atTop
        (𝓝 (upperMesh C a h N)) := by
    dsimp only [upperMesh]
    exact tendsto_finset_sum (Finset.range N) (by
      intro k _hk
      exact upperSeq_tendsto (C := C) (a := a) (h := h) ha hhpos k)
  have hsq_all :
      ∀ᶠ n : ℕ in atTop,
        ∀ k ∈ Finset.range N,
          lowerSeq C a h k n
            ≤ blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n ∧
          blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n
            ≤ upperSeq C a h k n := by
    rw [Filter.eventually_all_finset]
    intro k _hk
    exact weighted_block_squeeze_mesh (C := C) (a := a) (h := h) hC ha hhpos k
  have hlow_close :
      ∀ᶠ n : ℕ in atTop,
        |(∑ k ∈ Finset.range N, lowerSeq C a h k n) -
          lowerMesh C a h N| < ε := by
    simpa [Real.dist_eq] using
      hlow_tendsto.eventually (Metric.ball_mem_nhds (lowerMesh C a h N) hε)
  have hup_close :
      ∀ᶠ n : ℕ in atTop,
        |(∑ k ∈ Finset.range N, upperSeq C a h k n) -
          upperMesh C a h N| < ε := by
    simpa [Real.dist_eq] using
      hup_tendsto.eventually (Metric.ball_mem_nhds (upperMesh C a h N) hε)
  filter_upwards [hsq_all, hlow_close, hup_close] with n hsq hlow hup
  have hpartition :
      blockSum C a b n =
        ∑ k ∈ Finset.range N,
          blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n := by
    conv_lhs => rw [hb_eq]
    exact blockSum_arith_partition C a h hhnonneg N n
  have hlow_sum :
      (∑ k ∈ Finset.range N, lowerSeq C a h k n)
        ≤
      ∑ k ∈ Finset.range N,
        blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact (hsq k hk).1
  have hup_sum :
      (∑ k ∈ Finset.range N,
        blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n)
        ≤
      ∑ k ∈ Finset.range N, upperSeq C a h k n := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact (hsq k hk).2
  constructor
  · have hclose_lower :
        lowerMesh C a h N - ε
          <
        ∑ k ∈ Finset.range N, lowerSeq C a h k n := by
      have h1 := (abs_lt.mp hlow).1
      linarith
    rw [hpartition]
    exact le_trans hclose_lower.le hlow_sum
  · have hclose_upper :
        (∑ k ∈ Finset.range N, upperSeq C a h k n)
          <
        upperMesh C a h N + ε := by
      have h1 := (abs_lt.mp hup).2
      linarith
    rw [hpartition]
    exact le_trans hup_sum hclose_upper.le

end AnalyticCombinatorics.Ch8.Partitions.Erdos.Model
end
end

section
/-!
# The mesh estimate and the model-kernel window limit

The Riemann–Stieltjes mesh estimate: both endpoint sums `lowerMesh`/`upperMesh` on the
uniform mesh approximate `modelIntegral C a b = ∫ a..b (π²/6) y e^{−(C/2)y} dy` to any
tolerance for `N` large.  Proof: per-block sandwich `e^{−(C/2)α_{k+1}}·Q·Δ(y²) ≤
∫_block ≤ e^{−(C/2)α_k}·Q·Δ(y²)` (monotonicity of `e^{−x}`), and the upper−lower gap is
`≤ Σ (C/2)h·Q·2b·h = C·Q·b·(b−a)·h` by the Lipschitz bound `e^{−u}−e^{−v} ≤ v−u`.

Combined with the banked `blockSum_eventually_between_mesh_eps`, this yields the
model-kernel window limit `model_kernel_window`:

  `(1/n)·Σ_{(a√n,b√n]} σ(m)·e^{−(C/2)m/√n} → ∫_a^b (π²/6) y e^{−(C/2)y} dy`.

Opus-authored (replaces the mesh-estimate axiom in the ChatGPT draft with a real proof).
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter Finset intervalIntegral
open scoped BigOperators Topology Interval

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

/-- `π²/6 = 2Q`. -/
private lemma two_Q : Real.pi ^ 2 / 6 = 2 * Q := by
  simp only [Q]; ring

private lemma Q_pos' : (0 : ℝ) < Q := by
  simp only [Q]
  positivity

/-- The model density is interval-integrable. -/
private lemma density_intervalIntegrable (C α β : ℝ) :
    IntervalIntegrable (fun y : ℝ => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y))
      MeasureTheory.volume α β := by
  have hc : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y) := by
    have h1 : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y :=
      continuous_const.mul continuous_id
    have h2 : Continuous fun y : ℝ => Real.exp (-(C / 2) * y) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    exact h1.mul h2
  exact hc.intervalIntegrable α β

/-- Linear integrands are interval-integrable. -/
private lemma linear_intervalIntegrable (c α β : ℝ) :
    IntervalIntegrable (fun y : ℝ => c * y) MeasureTheory.volume α β :=
  (continuous_const.mul continuous_id).intervalIntegrable α β

/-- Lipschitz bound for `e^{−x}` on the nonnegative half-line. -/
private lemma exp_neg_sub_exp_neg_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.exp (-u) - Real.exp (-v) ≤ v - u := by
  have h1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : 1 - (v - u) ≤ Real.exp (-(v - u)) := by
    have := Real.add_one_le_exp (-(v - u))
    linarith
  have h4 : Real.exp (-(v - u)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 : Real.exp (-v) = Real.exp (-u) * Real.exp (-(v - u)) := by
    rw [← Real.exp_add]
    ring_nf
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h4), Real.exp_pos (-u)]

/-- The constant-exponential block integral: `∫_α^β (2QK)·y dy = QK(β²−α²)`. -/
private lemma block_const_integral (K α β : ℝ) :
    ∫ y in α..β, (2 * Q * K) * y = Q * K * (β ^ 2 - α ^ 2) := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-- Lower block bound: `e^{−(C/2)β}·Q·(β²−α²) ≤ ∫_α^β (π²/6) y e^{−(C/2)y} dy`. -/
private lemma block_lower_le_integral {C α β : ℝ} (hC : 0 < C) (hα : 0 ≤ α) (hαβ : α ≤ β) :
    Real.exp (-(C / 2) * β) * Q * (β ^ 2 - α ^ 2)
      ≤ ∫ y in α..β, (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y) := by
  have hK : Real.exp (-(C / 2) * β) * Q * (β ^ 2 - α ^ 2)
      = ∫ y in α..β, (2 * Q * Real.exp (-(C / 2) * β)) * y := by
    rw [block_const_integral]
    ring
  rw [hK]
  apply intervalIntegral.integral_mono_on hαβ
  · exact linear_intervalIntegrable _ _ _
  · exact density_intervalIntegrable _ _ _
  · intro y hy
    have hy0 : 0 ≤ y := le_trans hα hy.1
    have hexp : Real.exp (-(C / 2) * β) ≤ Real.exp (-(C / 2) * y) := by
      apply Real.exp_le_exp.mpr
      have h0 : 0 ≤ (C / 2) * (β - y) := mul_nonneg (by linarith) (by linarith [hy.2])
      nlinarith [h0]
    rw [two_Q]
    calc (2 * Q * Real.exp (-(C / 2) * β)) * y
        = (2 * Q * y) * Real.exp (-(C / 2) * β) := by ring
      _ ≤ (2 * Q * y) * Real.exp (-(C / 2) * y) := by
          apply mul_le_mul_of_nonneg_left hexp
          have := Q_pos'.le
          positivity
      _ = 2 * Q * y * Real.exp (-(C / 2) * y) := by ring

/-- Upper block bound: `∫_α^β (π²/6) y e^{−(C/2)y} dy ≤ e^{−(C/2)α}·Q·(β²−α²)`. -/
private lemma block_integral_le_upper {C α β : ℝ} (hC : 0 < C) (hα : 0 ≤ α) (hαβ : α ≤ β) :
    (∫ y in α..β, (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y))
      ≤ Real.exp (-(C / 2) * α) * Q * (β ^ 2 - α ^ 2) := by
  have hK : Real.exp (-(C / 2) * α) * Q * (β ^ 2 - α ^ 2)
      = ∫ y in α..β, (2 * Q * Real.exp (-(C / 2) * α)) * y := by
    rw [block_const_integral]
    ring
  rw [hK]
  apply intervalIntegral.integral_mono_on hαβ
  · exact density_intervalIntegrable _ _ _
  · exact linear_intervalIntegrable _ _ _
  · intro y hy
    have hy0 : 0 ≤ y := le_trans hα hy.1
    have hexp : Real.exp (-(C / 2) * y) ≤ Real.exp (-(C / 2) * α) := by
      apply Real.exp_le_exp.mpr
      have h0 : 0 ≤ (C / 2) * (y - α) := mul_nonneg (by linarith) (by linarith [hy.1])
      nlinarith [h0]
    rw [two_Q]
    calc 2 * Q * y * Real.exp (-(C / 2) * y)
        = (2 * Q * y) * Real.exp (-(C / 2) * y) := by ring
      _ ≤ (2 * Q * y) * Real.exp (-(C / 2) * α) := by
          apply mul_le_mul_of_nonneg_left hexp
          have := Q_pos'.le
          positivity
      _ = (2 * Q * Real.exp (-(C / 2) * α)) * y := by ring

/-- Mesh points are monotone in the index (for `h ≥ 0`). -/
private lemma meshPoint_mono {a h : ℝ} (hh : 0 ≤ h) {k N : ℕ} (hkN : k ≤ N) :
    meshPoint a h k ≤ meshPoint a h N := by
  dsimp [meshPoint]
  have hcast : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
  have := mul_le_mul_of_nonneg_right hcast hh
  linarith

/-- The right end of the mesh is `b` when `h = (b−a)/N`. -/
private lemma meshPoint_last {a b : ℝ} {N : ℕ} (hN : 0 < N) :
    meshPoint a ((b - a) / (N : ℝ)) N = b := by
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  dsimp [meshPoint]
  field_simp
  ring

/-- The integral splits over the mesh and is sandwiched by the endpoint sums. -/
private lemma mesh_sandwich {C a b : ℝ} (hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
    {N : ℕ} (hN : 0 < N) :
    lowerMesh C a ((b - a) / (N : ℝ)) N ≤ modelIntegral C a b ∧
      modelIntegral C a b ≤ upperMesh C a ((b - a) / (N : ℝ)) N := by
  set h : ℝ := (b - a) / (N : ℝ) with hdef
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hhnonneg : 0 ≤ h := by
    rw [hdef]
    have : 0 ≤ b - a := by linarith
    positivity
  have hlast : meshPoint a h N = b := meshPoint_last hN
  have hfirst : meshPoint a h 0 = a := by simp [meshPoint]
  -- split the integral over the mesh
  have hsplit :
      (∑ k ∈ Finset.range N,
        ∫ y in meshPoint a h k..meshPoint a h (k + 1),
          (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y))
        = modelIntegral C a b := by
    have := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k => meshPoint a h k) (n := N)
      (f := fun y => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y))
      (fun k _hk => density_intervalIntegrable C _ _)
    rw [this]
    dsimp only
    rw [hfirst, hlast]
    rfl
  constructor
  · -- lowerMesh ≤ ∫
    rw [← hsplit, lowerMesh]
    refine Finset.sum_le_sum ?_
    intro k _hk
    have hαk : 0 ≤ meshPoint a h k := meshPoint_nonneg ha hhnonneg k
    have hαβ : meshPoint a h k ≤ meshPoint a h (k + 1) :=
      meshPoint_mono hhnonneg (Nat.le_succ k)
    exact block_lower_le_integral hC hαk hαβ
  · -- ∫ ≤ upperMesh
    rw [← hsplit, upperMesh]
    refine Finset.sum_le_sum ?_
    intro k _hk
    have hαk : 0 ≤ meshPoint a h k := meshPoint_nonneg ha hhnonneg k
    have hαβ : meshPoint a h k ≤ meshPoint a h (k + 1) :=
      meshPoint_mono hhnonneg (Nat.le_succ k)
    exact block_integral_le_upper hC hαk hαβ

/-- The upper−lower mesh gap is at most `C·Q·b·(b−a)·h`. -/
private lemma mesh_gap_le {C a b : ℝ} (hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
    {N : ℕ} (hN : 0 < N) :
    upperMesh C a ((b - a) / (N : ℝ)) N - lowerMesh C a ((b - a) / (N : ℝ)) N
      ≤ C * Q * b * (b - a) * ((b - a) / (N : ℝ)) := by
  set h : ℝ := (b - a) / (N : ℝ) with hdef
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hhnonneg : 0 ≤ h := by
    rw [hdef]
    have : 0 ≤ b - a := by linarith
    positivity
  have hNh : (N : ℝ) * h = b - a := by
    rw [hdef]
    field_simp
  have hlast : meshPoint a h N = b := meshPoint_last hN
  have hb_pos : 0 < b := lt_of_le_of_lt ha hab
  -- per-term bound
  have hterm : ∀ k ∈ Finset.range N,
      Real.exp (-(C / 2) * meshPoint a h k) * Q *
          (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2) -
        Real.exp (-(C / 2) * meshPoint a h (k + 1)) * Q *
          (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2)
        ≤ (C / 2) * h * (Q * (2 * b * h)) := by
    intro k hk
    have hkN : k + 1 ≤ N := Finset.mem_range.mp hk
    have hαk : 0 ≤ meshPoint a h k := meshPoint_nonneg ha hhnonneg k
    have hαk1 : 0 ≤ meshPoint a h (k + 1) := meshPoint_nonneg ha hhnonneg (k + 1)
    have hαβ : meshPoint a h k ≤ meshPoint a h (k + 1) :=
      meshPoint_mono hhnonneg (Nat.le_succ k)
    have hkb : meshPoint a h k ≤ b := by
      rw [← hlast]
      exact meshPoint_mono hhnonneg (le_trans (Nat.le_succ k) hkN)
    have hk1b : meshPoint a h (k + 1) ≤ b := by
      rw [← hlast]
      exact meshPoint_mono hhnonneg hkN
    have hstep : meshPoint a h (k + 1) - meshPoint a h k = h := by
      dsimp [meshPoint]
      push_cast
      ring
    -- Lipschitz bound on the exponential difference
    have hlip :
        Real.exp (-(C / 2) * meshPoint a h k) -
            Real.exp (-(C / 2) * meshPoint a h (k + 1))
          ≤ (C / 2) * h := by
      have hu : 0 ≤ (C / 2) * meshPoint a h k := by positivity
      have huv : (C / 2) * meshPoint a h k ≤ (C / 2) * meshPoint a h (k + 1) :=
        mul_le_mul_of_nonneg_left hαβ (by positivity)
      have := exp_neg_sub_exp_neg_le hu huv
      have heq1 : -(C / 2) * meshPoint a h k = -((C / 2) * meshPoint a h k) := by ring
      have heq2 : -(C / 2) * meshPoint a h (k + 1) =
          -((C / 2) * meshPoint a h (k + 1)) := by ring
      rw [heq1, heq2]
      calc Real.exp (-((C / 2) * meshPoint a h k)) -
              Real.exp (-((C / 2) * meshPoint a h (k + 1)))
          ≤ (C / 2) * meshPoint a h (k + 1) - (C / 2) * meshPoint a h k := this
        _ = (C / 2) * (meshPoint a h (k + 1) - meshPoint a h k) := by ring
        _ = (C / 2) * h := by rw [hstep]
    -- the squared-difference factor
    have hsq : meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2 ≤ 2 * b * h := by
      have : meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2 =
          (meshPoint a h (k + 1) - meshPoint a h k) *
            (meshPoint a h (k + 1) + meshPoint a h k) := by ring
      rw [this, hstep]
      have hsum : meshPoint a h (k + 1) + meshPoint a h k ≤ 2 * b := by linarith
      calc h * (meshPoint a h (k + 1) + meshPoint a h k)
          ≤ h * (2 * b) := mul_le_mul_of_nonneg_left hsum hhnonneg
        _ = 2 * b * h := by ring
    have hsq_nonneg : 0 ≤ meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2 := by
      nlinarith [hαβ, hαk]
    have hexp_diff_nonneg :
        0 ≤ Real.exp (-(C / 2) * meshPoint a h k) -
            Real.exp (-(C / 2) * meshPoint a h (k + 1)) := by
      have : -(C / 2) * meshPoint a h (k + 1) ≤ -(C / 2) * meshPoint a h k := by
        nlinarith [hαβ]
      linarith [Real.exp_le_exp.mpr this]
    have hQ := Q_pos'.le
    calc Real.exp (-(C / 2) * meshPoint a h k) * Q *
            (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2) -
          Real.exp (-(C / 2) * meshPoint a h (k + 1)) * Q *
            (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2)
        = (Real.exp (-(C / 2) * meshPoint a h k) -
            Real.exp (-(C / 2) * meshPoint a h (k + 1))) * Q *
            (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2) := by ring
      _ ≤ ((C / 2) * h) * Q * (2 * b * h) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hlip hQ
          · exact hsq
          · exact hsq_nonneg
          · positivity
      _ = (C / 2) * h * (Q * (2 * b * h)) := by ring
  -- sum the per-term bounds
  have hsum_le :
      upperMesh C a h N - lowerMesh C a h N
        ≤ (N : ℝ) * ((C / 2) * h * (Q * (2 * b * h))) := by
    rw [upperMesh, lowerMesh, ← Finset.sum_sub_distrib]
    calc (∑ k ∈ Finset.range N,
          (Real.exp (-(C / 2) * meshPoint a h k) * Q *
              (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2) -
            Real.exp (-(C / 2) * meshPoint a h (k + 1)) * Q *
              (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2)))
        ≤ ∑ _k ∈ Finset.range N, (C / 2) * h * (Q * (2 * b * h)) :=
          Finset.sum_le_sum hterm
      _ = (N : ℝ) * ((C / 2) * h * (Q * (2 * b * h))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc upperMesh C a h N - lowerMesh C a h N
      ≤ (N : ℝ) * ((C / 2) * h * (Q * (2 * b * h))) := hsum_le
    _ = C * Q * b * ((N : ℝ) * h) * h := by ring
    _ = C * Q * b * (b - a) * h := by rw [hNh]

/--
**The mesh estimate** (formerly the draft's axiom): for every `ε > 0` there is a mesh
size `N` for which both endpoint sums are within `ε` of the model integral.
-/
theorem mesh_endpoint_sums_approx_integral
    {C : ℝ} (hC : 0 < C) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∀ ε > 0, ∃ N : ℕ, 0 < N ∧
      upperMesh C a ((b - a) / (N : ℝ)) N
        ≤ modelIntegral C a b + ε ∧
      modelIntegral C a b - ε
        ≤ lowerMesh C a ((b - a) / (N : ℝ)) N := by
  intro ε hε
  have hb_pos : 0 < b := lt_of_le_of_lt ha hab
  obtain ⟨M, hM⟩ := exists_nat_gt (C * Q * b * (b - a) ^ 2 / ε)
  refine ⟨M + 1, Nat.succ_pos M, ?_⟩
  set N : ℕ := M + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos M
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMN : C * Q * b * (b - a) ^ 2 / ε < (N : ℝ) := by
    have : (M : ℝ) < (N : ℝ) := by
      rw [hNdef]
      push_cast
      linarith
    linarith
  -- the gap bound is < ε for this N
  have hgap_lt : C * Q * b * (b - a) * ((b - a) / (N : ℝ)) < ε := by
    have hkey : C * Q * b * (b - a) ^ 2 < (N : ℝ) * ε := by
      have := (div_lt_iff₀ hε).mp hMN
      linarith [this]
    have hform : C * Q * b * (b - a) * ((b - a) / (N : ℝ))
        = (C * Q * b * (b - a) ^ 2) / (N : ℝ) := by
      ring
    rw [hform, div_lt_iff₀ hNposR]
    linarith [hkey]
  obtain ⟨hlow_le, hle_up⟩ := mesh_sandwich (C := C) hC ha hab hN
  have hgap := mesh_gap_le (C := C) hC ha hab hN
  constructor
  · -- upperMesh ≤ ∫ + ε
    linarith
  · -- ∫ − ε ≤ lowerMesh
    linarith

/--
**The model-kernel window limit** (HR Stage I.3, final assembly):

  `(1/n) Σ_{(a√n, b√n]} σ(m) e^{−(C/2)m/√n} → ∫_a^b (π²/6) y e^{−(C/2)y} dy`.
-/
theorem model_kernel_window
    {C : ℝ} (hC : 0 < C) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    Tendsto (blockSum C a b) atTop (𝓝 (modelIntegral C a b)) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨N, hNpos, hUpper, hLower⟩ :=
    mesh_endpoint_sums_approx_integral hC a b ha hab (ε / 3) hε3
  have hevent :=
    blockSum_eventually_between_mesh_eps
      (C := C) (a := a) (b := b) hC ha hab hNpos hε3
  rcases eventually_atTop.1 hevent with ⟨N0, hN0⟩
  refine ⟨N0, fun n hn => ?_⟩
  have hb := hN0 n hn
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [hb.1]
  · linarith [hb.2]

end AnalyticCombinatorics.Ch8.Partitions.Erdos.Model
end
end

/-!
# The true-kernel window limit

`Σ_{(a√n, b√n]} erdosWeight n m → ∫_a^b (π²/6) y e^{−(C/2)y} dy`.

Conversion of the model kernel to the true Erdős kernel via the banked uniform window
replacements: `1/(n−m) = 1/n + O(b/n^{3/2})` (`inv_window_approx`) and
`√n − √(n−m) = m/(2√n) + O(b²/√n)·(1/√n)` (`sqrt_diff_window_approx`), with all
exponentials `≤ 1` on the window.  Per-term difference `≤ σ(m)·D/n^{3/2}`; summed against
the quadratic divisor bound `Σ_{m ≤ b√n} σ(m) ≤ B b² n` this is `O(1/√n) → 0`, and
`model_kernel_window` finishes.  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

local notation "σR" => Sigma.sigmaR

/-- Lipschitz bound for `e^{−x}` on the nonnegative half-line (local copy). -/
private lemma exp_neg_sub_exp_neg_le' {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.exp (-u) - Real.exp (-v) ≤ v - u := by
  have h1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : 1 - (v - u) ≤ Real.exp (-(v - u)) := by
    have := Real.add_one_le_exp (-(v - u))
    linarith
  have h4 : Real.exp (-(v - u)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 : Real.exp (-v) = Real.exp (-u) * Real.exp (-(v - u)) := by
    rw [← Real.exp_add]
    ring_nf
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h4), Real.exp_pos (-u)]

/-- `|e^x − e^y| ≤ |x − y|` for `x, y ≤ 0`. -/
private lemma abs_exp_sub_exp_le {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  rcases le_total y x with h | h
  · have hle : Real.exp y ≤ Real.exp x := Real.exp_le_exp.mpr h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    have h2 := exp_neg_sub_exp_neg_le' (u := -x) (v := -y) (by linarith) (by linarith)
    simp only [neg_neg] at h2
    linarith
  · have hle : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    have h2 := exp_neg_sub_exp_neg_le' (u := -y) (v := -x) (by linarith) (by linarith)
    simp only [neg_neg] at h2
    linarith

/--
Per-term difference bound on the window: for `2m ≤ n`, `m ≤ b√n`,

  `|erdosWeight n m − σ(m)·e^{−(C/2)m/√n}·(1/n)| ≤ σ(m)·(2b + Cb²/2)/(n√n)`.
-/
private lemma kernel_term_diff_bound {b : ℝ} (hb : 0 < b) {n m : ℕ}
    (hn : 1 ≤ n) (h2m : 2 * m ≤ n)
    (hwin : (m : ℝ) ≤ b * Real.sqrt (n : ℝ)) :
    |erdosWeight n m -
        σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) * (1 / (n : ℝ))|
      ≤ σR m * ((2 * b + C * b ^ 2 / 2) / ((n : ℝ) * Real.sqrt (n : ℝ))) := by
  have hC := C_pos
  have hm_le : m ≤ n := le_trans (by omega) h2m
  have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hs : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnposR
  have hσ : (0 : ℝ) ≤ σR m := sigmaR_nonneg m
  have hsub_le : Real.sqrt ((n - m : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.sub_le n m
  -- the two exponentials
  set w : ℝ := Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) with hwdef
  set md : ℝ := Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) with hmddef
  have hw_pos : 0 < w := Real.exp_pos _
  have hw_le_one : w ≤ 1 := by
    rw [hwdef, Real.exp_le_one_iff]
    nlinarith [hsub_le, hC]
  -- decomposition
  have hdecomp :
      erdosWeight n m - σR m * md * (1 / (n : ℝ))
        = σR m * ((1 / ((n - m : ℕ) : ℝ) - 1 / (n : ℝ)) * w)
          + σR m * ((w - md) * (1 / (n : ℝ))) := by
    unfold erdosWeight
    rw [← hwdef]
    ring
  -- the reciprocal replacement
  have h1 : |1 / (((n - m : ℕ) : ℝ)) - 1 / (n : ℝ)|
      ≤ 2 * b / ((n : ℝ) * Real.sqrt (n : ℝ)) :=
    inv_window_approx hb.le h2m hn hwin
  -- the exponent replacement
  have h2 : |w - md| ≤ C * (b ^ 2 / (2 * Real.sqrt (n : ℝ))) := by
    have hx : -C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)) ≤ 0 := by
      nlinarith [hsub_le, hC]
    have hy : -(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ) ≤ 0 := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hnum : -(C / 2) * (m : ℝ) ≤ 0 := by nlinarith [hC]
      exact div_nonpos_of_nonpos_of_nonneg hnum hs.le
    have habs := abs_exp_sub_exp_le hx hy
    have heq :
        -C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
            - (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ))
          = -C * ((Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
              - (m : ℝ) / (2 * Real.sqrt (n : ℝ))) := by
      field_simp
      ring
    calc |w - md| ≤ |(-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)))
            - (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ))| := habs
      _ = C * |(Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
            - (m : ℝ) / (2 * Real.sqrt (n : ℝ))| := by
          rw [heq, abs_mul, abs_neg, abs_of_pos hC]
      _ ≤ C * (b ^ 2 / (2 * Real.sqrt (n : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (sqrt_diff_window_approx hb.le hm_le hn hwin) hC.le
  -- assemble
  rw [hdecomp]
  have hterm1 : |σR m * ((1 / ((n - m : ℕ) : ℝ) - 1 / (n : ℝ)) * w)|
      ≤ σR m * (2 * b / ((n : ℝ) * Real.sqrt (n : ℝ))) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hσ, abs_of_pos hw_pos]
    have hmm : |1 / ((n - m : ℕ) : ℝ) - 1 / (n : ℝ)| * w
        ≤ (2 * b / ((n : ℝ) * Real.sqrt (n : ℝ))) * 1 :=
      mul_le_mul h1 hw_le_one hw_pos.le (by positivity)
    calc σR m * (|1 / ((n - m : ℕ) : ℝ) - 1 / (n : ℝ)| * w)
        ≤ σR m * ((2 * b / ((n : ℝ) * Real.sqrt (n : ℝ))) * 1) :=
          mul_le_mul_of_nonneg_left hmm hσ
      _ = σR m * (2 * b / ((n : ℝ) * Real.sqrt (n : ℝ))) := by ring
  have hterm2 : |σR m * ((w - md) * (1 / (n : ℝ)))|
      ≤ σR m * (C * b ^ 2 / 2 / ((n : ℝ) * Real.sqrt (n : ℝ))) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hσ,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ))]
    have hstep : |w - md| * (1 / (n : ℝ))
        ≤ C * (b ^ 2 / (2 * Real.sqrt (n : ℝ))) * (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    calc σR m * (|w - md| * (1 / (n : ℝ)))
        ≤ σR m * (C * (b ^ 2 / (2 * Real.sqrt (n : ℝ))) * (1 / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep hσ
      _ = σR m * (C * b ^ 2 / 2 / ((n : ℝ) * Real.sqrt (n : ℝ))) := by
          field_simp
  calc |σR m * ((1 / ((n - m : ℕ) : ℝ) - 1 / (n : ℝ)) * w)
        + σR m * ((w - md) * (1 / (n : ℝ)))|
      ≤ |σR m * ((1 / ((n - m : ℕ) : ℝ) - 1 / (n : ℝ)) * w)|
        + |σR m * ((w - md) * (1 / (n : ℝ)))| := abs_add_le _ _
    _ ≤ σR m * (2 * b / ((n : ℝ) * Real.sqrt (n : ℝ)))
        + σR m * (C * b ^ 2 / 2 / ((n : ℝ) * Real.sqrt (n : ℝ))) := by
        linarith [hterm1, hterm2]
    _ = σR m * ((2 * b + C * b ^ 2 / 2) / ((n : ℝ) * Real.sqrt (n : ℝ))) := by
        ring

/-- The masked divisor mass on the window is at most `B·b²·n`. -/
private lemma window_sigma_mass_le {a b : ℝ} (hb : 0 < b) {B : ℝ}
    (hB : ∀ N : ℕ, (∑ m ∈ Finset.Icc 1 N, σR m) ≤ B * (N : ℝ) ^ 2)
    (hBpos : 0 < B) (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
      (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
       then σR m else 0))
      ≤ B * b ^ 2 * (n : ℝ) := by
  classical
  have hsn : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsub :
      (Finset.Icc 1 (n - 1)).filter
          (fun m : ℕ => a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ b * Real.sqrt (n : ℝ))
        ⊆ Finset.Icc 1 ⌊b * Real.sqrt (n : ℝ)⌋₊ := by
    intro m hm
    obtain ⟨hmIcc, hwin⟩ := Finset.mem_filter.mp hm
    have h1 : 1 ≤ m := (Finset.mem_Icc.mp hmIcc).1
    have h2 : m ≤ ⌊b * Real.sqrt (n : ℝ)⌋₊ := Nat.le_floor hwin.2
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  calc (∑ m ∈ Finset.Icc 1 (n - 1),
        (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ b * Real.sqrt (n : ℝ) then σR m else 0))
      = ∑ m ∈ (Finset.Icc 1 (n - 1)).filter
          (fun m : ℕ => a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ b * Real.sqrt (n : ℝ)), σR m := by
        rw [Finset.sum_filter]
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊b * Real.sqrt (n : ℝ)⌋₊, σR m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun m _ _ => sigmaR_nonneg m)
    _ ≤ B * (⌊b * Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ 2 := hB _
    _ ≤ B * (b * Real.sqrt (n : ℝ)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hBpos.le
        have hfl : ((⌊b * Real.sqrt (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ b * Real.sqrt (n : ℝ) :=
          Nat.floor_le (by positivity)
        have h0 : (0 : ℝ) ≤ (⌊b * Real.sqrt (n : ℝ)⌋₊ : ℝ) := Nat.cast_nonneg _
        nlinarith [hfl, h0]
    _ = B * b ^ 2 * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
    _ = B * b ^ 2 * (n : ℝ) := by
        rw [Real.mul_self_sqrt (Nat.cast_nonneg n)]

end AnalyticCombinatorics.Ch8.Partitions.Erdos.Model
end

section
open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos AnalyticCombinatorics.Ch8.Partitions.Erdos.Model
set_option maxHeartbeats 800000
open Filter Finset
open scoped BigOperators Topology
local notation "σR" => Sigma.sigmaR
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Tendsto
      (fun n : ℕ => ∑ m ∈ Finset.Icc 1 (n - 1),
        (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
         then erdosWeight n m else 0))
      atTop (𝓝 (modelIntegral C a b)) := by
  classical
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hC := C_pos
  obtain ⟨B, hBpos, hB⟩ := sigma_summatory_quadratic_bound
  set D : ℝ := 2 * b + C * b ^ 2 / 2 with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    positivity
  have hmodel := model_kernel_window (C := C) hC a b ha hab
  -- the difference tends to 0
  have hdiff :
      Tendsto
        (fun n : ℕ =>
          (∑ m ∈ Finset.Icc 1 (n - 1),
            (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
             then erdosWeight n m else 0))
            - blockSum C a b n)
        atTop (𝓝 0) := by
    -- squeeze against (B·b²·D)/√n
    have hbound : ∀ᶠ n : ℕ in atTop,
        ‖(∑ m ∈ Finset.Icc 1 (n - 1),
            (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
             then erdosWeight n m else 0))
            - blockSum C a b n‖
          ≤ (B * b ^ 2 * D) / Real.sqrt (n : ℝ) := by
      have hev : ∀ᶠ n : ℕ in atTop, (⌈(4 : ℝ) * b ^ 2⌉₊ ≤ n ∧ 1 ≤ n) := by
        filter_upwards [eventually_ge_atTop ⌈(4 : ℝ) * b ^ 2⌉₊,
          eventually_ge_atTop 1] with n h1 h2
        exact ⟨h1, h2⟩
      filter_upwards [hev] with n ⟨hn4, hn1⟩
      have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hs : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnposR
      have hn4R : (4 : ℝ) * b ^ 2 ≤ (n : ℝ) := by
        calc (4 : ℝ) * b ^ 2 ≤ (⌈(4 : ℝ) * b ^ 2⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn4
      -- on the window, 2m ≤ n
      have h2m : ∀ m : ℕ, (m : ℝ) ≤ b * Real.sqrt (n : ℝ) → 2 * m ≤ n := by
        intro m hm
        have h2b : 2 * b ≤ Real.sqrt (n : ℝ) := by
          have h2b0 : (0 : ℝ) ≤ 2 * b := by positivity
          calc 2 * b = Real.sqrt ((2 * b) ^ 2) := (Real.sqrt_sq h2b0).symm
            _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
        have : 2 * (m : ℝ) ≤ (n : ℝ) := by
          calc 2 * (m : ℝ) ≤ 2 * (b * Real.sqrt (n : ℝ)) := by linarith
            _ = (2 * b) * Real.sqrt (n : ℝ) := by ring
            _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
                mul_le_mul_of_nonneg_right h2b hs.le
            _ = (n : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg n)
        exact_mod_cast this
      -- blockSum as a termwise-masked sum
      have hblock :
          blockSum C a b n =
            ∑ m ∈ Finset.Icc 1 (n - 1),
              (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                  (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
               then σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
                  (1 / (n : ℝ))
               else 0) := by
        rw [blockSum, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro m _hm
        by_cases hwin : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
        · rw [if_pos hwin, if_pos hwin]
          ring
        · rw [if_neg hwin, if_neg hwin, mul_zero]
      -- difference as one masked sum
      have hsumdiff :
          (∑ m ∈ Finset.Icc 1 (n - 1),
            (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
             then erdosWeight n m else 0))
            - blockSum C a b n
          = ∑ m ∈ Finset.Icc 1 (n - 1),
              (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                  (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
               then erdosWeight n m -
                  σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
                    (1 / (n : ℝ))
               else 0) := by
        rw [hblock, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro m _hm
        by_cases hwin : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
        · rw [if_pos hwin, if_pos hwin, if_pos hwin]
        · rw [if_neg hwin, if_neg hwin, if_neg hwin, sub_zero]
      rw [hsumdiff, Real.norm_eq_abs]
      -- triangle inequality + per-term bound + mass bound
      calc |∑ m ∈ Finset.Icc 1 (n - 1),
            (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
             then erdosWeight n m -
                σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
                  (1 / (n : ℝ))
             else 0)|
          ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
              |if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                  (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
               then erdosWeight n m -
                  σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
                    (1 / (n : ℝ))
               else 0| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
              (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                  (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
               then σR m * (D / ((n : ℝ) * Real.sqrt (n : ℝ)))
               else 0) := by
            refine Finset.sum_le_sum ?_
            intro m _hm
            by_cases hwin : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
            · rw [if_pos hwin, if_pos hwin]
              exact kernel_term_diff_bound hb hn1 (h2m m hwin.2) hwin.2
            · rw [if_neg hwin, if_neg hwin, abs_zero]
        _ = (D / ((n : ℝ) * Real.sqrt (n : ℝ))) *
              ∑ m ∈ Finset.Icc 1 (n - 1),
                (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                    (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
                 then σR m else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro m _hm
            by_cases hwin : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
            · rw [if_pos hwin, if_pos hwin]
              ring
            · rw [if_neg hwin, if_neg hwin, mul_zero]
        _ ≤ (D / ((n : ℝ) * Real.sqrt (n : ℝ))) * (B * b ^ 2 * (n : ℝ)) := by
            apply mul_le_mul_of_nonneg_left
              (window_sigma_mass_le (a := a) hb hB hBpos n)
            positivity
        _ = (B * b ^ 2 * D) / Real.sqrt (n : ℝ) := by
            field_simp
    -- the bound tends to zero
    have hzero :
        Tendsto (fun n : ℕ => (B * b ^ 2 * D) / Real.sqrt (n : ℝ))
          atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    exact squeeze_zero_norm' hbound hzero
  -- combine: trueSum = (trueSum − blockSum) + blockSum
  have hcomb := hdiff.add hmodel
  rw [zero_add] at hcomb
  have hfun :
      (fun n : ℕ =>
        ((∑ m ∈ Finset.Icc 1 (n - 1),
          (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
              (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
           then erdosWeight n m else 0))
          - blockSum C a b n) + blockSum C a b n)
      = fun n : ℕ =>
          ∑ m ∈ Finset.Icc 1 (n - 1),
            (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
             then erdosWeight n m else 0) := by
    funext n
    ring
  rwa [hfun] at hcomb
end
