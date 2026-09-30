-- Prove2me | solution 1 for lean_workbook_plus_13803
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:39:02.473351+00:00
-- url     : https://prove2.me/submissions/51fdabb4-6025-407e-8c87-7fc36a41b830

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

noncomputable def dilogTerm (q : ℝ) (n : ℕ) : ℝ := q ^ n / (n : ℝ) ^ 2

theorem dilog_term_norm (q : ℝ) (n : ℕ) :
    ‖dilogTerm q n‖ = |q| ^ n / (n : ℝ) ^ 2 := by
  simp only [dilogTerm, norm_div, norm_pow, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]

theorem dilog_unit_majorant (q : ℝ) (hq : |q| ≤ 1) (n : ℕ) :
    ‖dilogTerm q n‖ ≤ 1 / (n : ℝ) ^ 2 := by
  rw [dilog_term_norm]
  exact div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg q) hq)
    (sq_nonneg (n : ℝ))

theorem dilog_summable_of_abs_le_one (q : ℝ) (hq : |q| ≤ 1) : Summable (dilogTerm q) :=
  hasSum_zeta_two.summable.of_norm_bounded (dilog_unit_majorant q hq)

theorem dilog_outside_norm_tendsto (q : ℝ) (hq : 1 < |q|) :
    Tendsto (fun n => ‖dilogTerm q n‖) atTop atTop := by
  have hp : 0 < |q| := lt_trans zero_lt_one hq
  have hlog : 0 < Real.log |q| := Real.log_pos hq
  have h := (tendsto_exp_mul_div_rpow_atTop 2 (Real.log |q|) hlog).comp
    tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards with n
  rw [dilog_term_norm]
  simp only [Function.comp_apply, Real.rpow_two, mul_comm (Real.log |q|) (n : ℝ), Real.exp_nat_mul,
    Real.exp_log hp]

theorem dilog_summable_iff (q : ℝ) : Summable (dilogTerm q) ↔ |q| ≤ 1 := by
  constructor
  · intro hs
    by_contra! hq
    have hz : Tendsto (fun n => ‖dilogTerm q n‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hs.tendsto_atTop_zero.norm
    exact not_tendsto_nhds_of_tendsto_atTop (dilog_outside_norm_tendsto q hq) 0 hz
  · exact dilog_summable_of_abs_le_one q

theorem dilog_partial_sums_converge_iff (q : ℝ) :
    (∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, dilogTerm q n) atTop (𝓝 L)) ↔
      |q| ≤ 1 := by
  constructor
  · rintro ⟨L, hL⟩
    by_contra! hq
    have hshift := (tendsto_add_atTop_iff_nat 1).mpr hL
    have hz : Tendsto (dilogTerm q) atTop (𝓝 0) := by
      simpa only [Finset.sum_range_succ, add_sub_cancel_left, sub_self] using hshift.sub hL
    have hnorm : Tendsto (fun n => ‖dilogTerm q n‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hz.norm
    exact not_tendsto_nhds_of_tendsto_atTop (dilog_outside_norm_tendsto q hq) 0 hnorm
  · intro hq
    exact ⟨_, (dilog_summable_of_abs_le_one q hq).hasSum.tendsto_sum_nat⟩

theorem dilog_uniform_convergence :
    TendstoUniformlyOn (fun N q => ∑ n ∈ Finset.range N, dilogTerm q n)
      (fun q => ∑' n, dilogTerm q n) atTop (Set.Icc (-1 : ℝ) 1) := by
  apply tendstoUniformlyOn_tsum_nat hasSum_zeta_two.summable
  intro n q hq
  exact dilog_unit_majorant q (abs_le.mpr hq) n

theorem dilog_uniform_absolute_convergence :
    TendstoUniformlyOn (fun N q => ∑ n ∈ Finset.range N, |dilogTerm q n|)
      (fun q => ∑' n, |dilogTerm q n|) atTop (Set.Icc (-1 : ℝ) 1) := by
  apply tendstoUniformlyOn_tsum_nat hasSum_zeta_two.summable
  intro n q hq
  simpa only [Real.norm_eq_abs, abs_abs] using dilog_unit_majorant q (abs_le.mpr hq) n

theorem dilog_continuousOn :
    ContinuousOn (fun q => ∑' n, dilogTerm q n) (Set.Icc (-1 : ℝ) 1) := by
  have hc : ∀ n : ℕ, ContinuousOn (fun q => dilogTerm q n) (Set.Icc (-1 : ℝ) 1) :=
    fun n => ((continuous_pow n).div_const ((n : ℝ) ^ 2)).continuousOn
  exact continuousOn_tsum hc hasSum_zeta_two.summable
    (fun n q hq => dilog_unit_majorant q (abs_le.mpr hq) n)

theorem dilog_positive_endpoint : HasSum (dilogTerm 1) (Real.pi ^ 2 / 6) := by
  unfold dilogTerm
  simpa only [dilogTerm, one_pow] using hasSum_zeta_two

theorem reciprocal_square_even_hasSum :
    HasSum (fun n : ℕ => 1 / ((2 * n : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 24) := by
  have h := hasSum_zeta_two.mul_left (1 / 4 : ℝ)
  have hv : (1 / 4 : ℝ) * (Real.pi ^ 2 / 6) = Real.pi ^ 2 / 24 := by ring
  rw [hv] at h
  apply h.congr_fun
  intro n
  push_cast
  ring

theorem reciprocal_square_odd_hasSum :
    HasSum (fun n : ℕ => 1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 8) := by
  have hi : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro n m h
    change 2 * n + 1 = 2 * m + 1 at h
    omega
  have hs : Summable (fun n : ℕ => 1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2) :=
    hasSum_zeta_two.summable.comp_injective hi
  have hall : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2)
      (Real.pi ^ 2 / 24 + ∑' n : ℕ, 1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2) :=
    HasSum.even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ 2)
      reciprocal_square_even_hasSum hs.hasSum
  have heq := hasSum_zeta_two.unique hall
  have hval : (∑' n : ℕ, 1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2) = Real.pi ^ 2 / 8 := by
    linarith
  simpa only [hval] using hs.hasSum

theorem dilog_negative_endpoint : HasSum (dilogTerm (-1)) (-(Real.pi ^ 2) / 12) := by
  have he : HasSum (fun n => dilogTerm (-1) (2 * n)) (Real.pi ^ 2 / 24) := by
    simpa only [dilogTerm, pow_mul, neg_one_sq, one_pow] using reciprocal_square_even_hasSum
  have ho : HasSum (fun n => dilogTerm (-1) (2 * n + 1)) (-(Real.pi ^ 2 / 8)) := by
    simpa only [dilogTerm, pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul,
      neg_div] using reciprocal_square_odd_hasSum.neg
  have h := HasSum.even_add_odd (f := dilogTerm (-1)) he ho
  have hv : Real.pi ^ 2 / 24 + -(Real.pi ^ 2 / 8) = -(Real.pi ^ 2) / 12 := by ring
  rwa [hv] at h

theorem dilog_telescoping_majorant (a : ℝ) (ha : 0 < a) :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + a) * ((n : ℝ) + a + 1))) (1 / a) := by
  have hsum : ∀ N : ℕ,
      ∑ n ∈ Finset.range N, 1 / (((n : ℝ) + a) * ((n : ℝ) + a + 1)) =
        1 / a - 1 / ((N : ℝ) + a) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      have hd : 0 < (N : ℝ) + a := by positivity
      have hd' : 0 < (N : ℝ) + a + 1 := by positivity
      rw [show (N : ℝ) + 1 + a = (N : ℝ) + a + 1 by ring]
      field_simp <;> ring
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity) _).mpr
  have hden : Tendsto (fun N : ℕ => (N : ℝ) + a) atTop atTop :=
    tendsto_atTop_add_const_right atTop a tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => 1 / a - 1 / ((N : ℝ) + a)) atTop (𝓝 (1 / a)) := by
    simpa only [one_div, Pi.inv_apply, sub_zero] using
      (tendsto_const_nhds (x := 1 / a)).sub hden.inv_tendsto_atTop
  apply hlim.congr'
  filter_upwards with N
  exact (hsum N).symm

theorem dilog_uniform_tail_bound (q : ℝ) (hq : |q| ≤ 1) (N : ℕ) (hN : 0 < N) :
    |(∑' n, dilogTerm q n) - ∑ n ∈ Finset.range (N + 1), dilogTerm q n| ≤
      1 / (N : ℝ) := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs := dilog_summable_of_abs_le_one q hq
  have hsum := Summable.sum_add_tsum_nat_add (f := dilogTerm q) (N + 1) hs
  have heq : (∑' n, dilogTerm q n) - ∑ n ∈ Finset.range (N + 1), dilogTerm q n =
      ∑' i, dilogTerm q (i + (N + 1)) := by linarith
  rw [heq]
  change ‖∑' i, dilogTerm q (i + (N + 1))‖ ≤ _
  apply tsum_of_norm_bounded (dilog_telescoping_majorant (N : ℝ) hN')
  intro i
  apply (dilog_unit_majorant q hq (i + (N + 1))).trans
  push_cast
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [show (0 : ℝ) ≤ (i : ℝ) from Nat.cast_nonneg i]

theorem scaled_dilog_term (x : ℝ) (n : ℕ) :
    x ^ n / ((3 : ℝ) ^ n * (n : ℝ) ^ 2) = dilogTerm (x / 3) n := by
  unfold dilogTerm
  rw [div_pow]
  ring

theorem scaled_dilog_summable_iff (x : ℝ) :
    Summable (fun n : ℕ => x ^ n / ((3 : ℝ) ^ n * (n : ℝ) ^ 2)) ↔ |x| ≤ 3 := by
  simp_rw [scaled_dilog_term]
  rw [dilog_summable_iff, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3),
    div_le_iff₀ (by norm_num : (0 : ℝ) < 3), one_mul]

theorem scaled_dilog_uniform_convergence :
    TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range N,
      x ^ n / ((3 : ℝ) ^ n * (n : ℝ) ^ 2))
      (fun x => ∑' n : ℕ, x ^ n / ((3 : ℝ) ^ n * (n : ℝ) ^ 2))
      atTop (Set.Icc (-3 : ℝ) 3) := by
  apply tendstoUniformlyOn_tsum_nat hasSum_zeta_two.summable
  intro n x hx
  rw [scaled_dilog_term]
  apply dilog_unit_majorant
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3),
    div_le_iff₀ (by norm_num : (0 : ℝ) < 3), one_mul]
  exact abs_le.mpr hx

theorem scaled_dilog_uniform_absolute_convergence :
    TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range N,
      |x ^ n / ((3 : ℝ) ^ n * (n : ℝ) ^ 2)|)
      (fun x => ∑' n : ℕ, |x ^ n / ((3 : ℝ) ^ n * (n : ℝ) ^ 2)|)
      atTop (Set.Icc (-3 : ℝ) 3) := by
  apply tendstoUniformlyOn_tsum_nat hasSum_zeta_two.summable
  intro n x hx
  have hq : |x / 3| ≤ 1 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3),
      div_le_iff₀ (by norm_num : (0 : ℝ) < 3), one_mul]
    exact abs_le.mpr hx
  simpa only [scaled_dilog_term, Real.norm_eq_abs, abs_abs] using
    dilog_unit_majorant (x / 3) hq n

theorem scaled_dilog_uniform_tail_bound (x : ℝ) (hx : |x| ≤ 3) (N : ℕ) (hN : 0 < N) :
    |(∑' n : ℕ, x ^ n / ((3 : ℝ) ^ n * (n : ℝ) ^ 2)) -
      ∑ n ∈ Finset.range (N + 1), x ^ n / ((3 : ℝ) ^ n * (n : ℝ) ^ 2)| ≤ 1 / (N : ℝ) := by
  have hq : |x / 3| ≤ 1 := by
    rwa [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3),
      div_le_iff₀ (by norm_num : (0 : ℝ) < 3), one_mul]
  simpa only [scaled_dilog_term] using dilog_uniform_tail_bound (x / 3) hq N hN

theorem scaled_dilog_positive_endpoint :
    HasSum (fun n : ℕ => (3 : ℝ) ^ n / ((3 : ℝ) ^ n * (n : ℝ) ^ 2))
      (Real.pi ^ 2 / 6) := by
  simpa only [scaled_dilog_term, div_self (by norm_num : (3 : ℝ) ≠ 0)] using
    dilog_positive_endpoint

theorem scaled_dilog_negative_endpoint :
    HasSum (fun n : ℕ => (-3 : ℝ) ^ n / ((3 : ℝ) ^ n * (n : ℝ) ^ 2))
      (-(Real.pi ^ 2) / 12) := by
  simpa only [scaled_dilog_term, neg_div, div_self (by norm_num : (3 : ℝ) ≠ 0)] using
    dilog_negative_endpoint

theorem solution (x : ℝ) (hx : -3 < x ∧ x < 3) (n : ℕ) :
    ∃ y, ∑' n : ℕ, (x ^ n / (3 ^ n * n ^ 2)) = y := by
  have hs := (scaled_dilog_summable_iff x).mpr (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  exact ⟨_, hs.hasSum.tsum_eq⟩

#print axioms dilogTerm
#print axioms dilog_term_norm
#print axioms dilog_unit_majorant
#print axioms dilog_summable_of_abs_le_one
#print axioms dilog_outside_norm_tendsto
#print axioms dilog_summable_iff
#print axioms dilog_partial_sums_converge_iff
#print axioms dilog_uniform_convergence
#print axioms dilog_uniform_absolute_convergence
#print axioms dilog_continuousOn
#print axioms dilog_positive_endpoint
#print axioms reciprocal_square_even_hasSum
#print axioms reciprocal_square_odd_hasSum
#print axioms dilog_negative_endpoint
#print axioms dilog_telescoping_majorant
#print axioms dilog_uniform_tail_bound
#print axioms scaled_dilog_term
#print axioms scaled_dilog_summable_iff
#print axioms scaled_dilog_uniform_convergence
#print axioms scaled_dilog_uniform_absolute_convergence
#print axioms scaled_dilog_uniform_tail_bound
#print axioms scaled_dilog_positive_endpoint
#print axioms scaled_dilog_negative_endpoint
#print axioms solution
