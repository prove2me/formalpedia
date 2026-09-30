-- Prove2me | solution 1 for lean_workbook_plus_33707
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:41:43.140498+00:00
-- url     : https://prove2.me/submissions/c3ed1a36-22b0-4269-94b8-317140ddcf01

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

noncomputable def quadraticGeometricTerm (q : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ 2 * q ^ n

theorem quadratic_geometric_hasSum (q : ℝ) (hq : |q| < 1) :
    HasSum (quadraticGeometricTerm q) (q * (1 + q) / (1 - q) ^ 3) := by
  have hn : ‖q‖ < 1 := hq
  have hd : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr (lt_of_le_of_lt (le_abs_self q) hq))
  have h := ((hasSum_choose_mul_geometric_of_norm_lt_one 2 hn).mul_left 2).sub
    (((hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left 3).add
      ((hasSum_geometric_of_abs_lt_one hq).mul_left 2))
  have hv : 2 * (1 / (1 - q) ^ (2 + 1)) -
      (3 * (q / (1 - q) ^ 2) + 2 * (1 - q)⁻¹) =
      q * (1 + q) / (1 - q) ^ 3 := by field_simp; ring
  rw [hv] at h
  apply h.congr_fun
  intro n
  simp only [quadraticGeometricTerm, Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem quadratic_geometric_norm (q : ℝ) (n : ℕ) :
    ‖quadraticGeometricTerm q n‖ = (n : ℝ) ^ 2 * |q| ^ n := by
  simp only [quadraticGeometricTerm, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]

theorem quadratic_geometric_terms_vanish_iff (q : ℝ) :
    Tendsto (quadraticGeometricTerm q) atTop (𝓝 0) ↔ |q| < 1 := by
  constructor
  · intro h
    by_contra! hq
    have hz : Tendsto (fun n => ‖quadraticGeometricTerm q n‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using h.norm
    have hb : ∀ᶠ n : ℕ in atTop, 1 ≤ ‖quadraticGeometricTerm q n‖ := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [quadratic_geometric_norm]
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn') (one_le_pow₀ hq)
    have hf : (1 : ℝ) ≤ 0 := ge_of_tendsto hz hb
    norm_num at hf
  · intro hq
    exact (quadratic_geometric_hasSum q hq).summable.tendsto_atTop_zero

theorem quadratic_geometric_summable_iff (q : ℝ) :
    Summable (quadraticGeometricTerm q) ↔ |q| < 1 := by
  exact ⟨fun h => (quadratic_geometric_terms_vanish_iff q).mp h.tendsto_atTop_zero,
    fun h => (quadratic_geometric_hasSum q h).summable⟩

theorem quadratic_geometric_partial_sums_converge_iff (q : ℝ) :
    (∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, quadraticGeometricTerm q n)
      atTop (𝓝 L)) ↔ |q| < 1 := by
  constructor
  · rintro ⟨L, hL⟩
    apply (quadratic_geometric_terms_vanish_iff q).mp
    have hshift := (tendsto_add_atTop_iff_nat 1).mpr hL
    simpa only [Finset.sum_range_succ, add_sub_cancel_left, sub_self] using hshift.sub hL
  · intro hq
    exact ⟨_, (quadratic_geometric_hasSum q hq).tendsto_sum_nat⟩

theorem quadratic_geometric_tail_hasSum (q : ℝ) (hq : |q| < 1) (N : ℕ) :
    HasSum (fun n => quadraticGeometricTerm q (n + N))
      (q ^ N * ((N : ℝ) ^ 2 / (1 - q) +
        2 * (N : ℝ) * q / (1 - q) ^ 2 + q * (1 + q) / (1 - q) ^ 3)) := by
  have h := (((hasSum_geometric_of_abs_lt_one hq).mul_left ((N : ℝ) ^ 2)).add
    (((hasSum_coe_mul_geometric_of_norm_lt_one (show ‖q‖ < 1 from hq)).mul_left
      (2 * (N : ℝ))).add (quadratic_geometric_hasSum q hq))).mul_left (q ^ N)
  have hv : q ^ N * ((N : ℝ) ^ 2 * (1 - q)⁻¹ +
      (2 * (N : ℝ) * (q / (1 - q) ^ 2) + q * (1 + q) / (1 - q) ^ 3)) =
      q ^ N * ((N : ℝ) ^ 2 / (1 - q) + 2 * (N : ℝ) * q / (1 - q) ^ 2 +
        q * (1 + q) / (1 - q) ^ 3) := by ring
  rw [hv] at h
  apply h.congr_fun
  intro n
  simp only [quadraticGeometricTerm, Nat.cast_add, pow_add]
  ring

theorem quadratic_geometric_tail (q : ℝ) (hq : |q| < 1) (N : ℕ) :
    q * (1 + q) / (1 - q) ^ 3 - ∑ n ∈ Finset.range N, quadraticGeometricTerm q n =
      q ^ N * ((N : ℝ) ^ 2 / (1 - q) +
        2 * (N : ℝ) * q / (1 - q) ^ 2 + q * (1 + q) / (1 - q) ^ 3) := by
  have h := Summable.sum_add_tsum_nat_add (f := quadraticGeometricTerm q) N
    (quadratic_geometric_hasSum q hq).summable
  rw [(quadratic_geometric_hasSum q hq).tsum_eq,
    (quadratic_geometric_tail_hasSum q hq N).tsum_eq] at h
  linarith

theorem quadratic_geometric_majorant (q r : ℝ) (hq : |q| ≤ r) (n : ℕ) :
    ‖quadraticGeometricTerm q n‖ ≤ quadraticGeometricTerm r n := by
  rw [quadratic_geometric_norm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg q) hq n) (sq_nonneg (n : ℝ))

theorem quadratic_geometric_uniform (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    TendstoUniformlyOn (fun N q => ∑ n ∈ Finset.range N, quadraticGeometricTerm q n)
      (fun q => ∑' n, quadraticGeometricTerm q n) atTop (Set.Icc (-r) r) := by
  apply tendstoUniformlyOn_tsum_nat
    (quadratic_geometric_hasSum r (by simpa only [abs_of_nonneg hr] using hr1)).summable
  intro n q hq
  exact quadratic_geometric_majorant q r (abs_le.mpr hq) n

theorem quadratic_geometric_uniform_absolute (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    TendstoUniformlyOn (fun N q => ∑ n ∈ Finset.range N, |quadraticGeometricTerm q n|)
      (fun q => ∑' n, |quadraticGeometricTerm q n|) atTop (Set.Icc (-r) r) := by
  apply tendstoUniformlyOn_tsum_nat
    (quadratic_geometric_hasSum r (by simpa only [abs_of_nonneg hr] using hr1)).summable
  intro n q hq
  simpa only [Real.norm_eq_abs, abs_abs] using
    quadratic_geometric_majorant q r (abs_le.mpr hq) n

theorem quadratic_geometric_source_identity (x : ℝ) (n : ℕ) :
    (n : ℝ) ^ 2 * x ^ (2 * n) = quadraticGeometricTerm (x ^ 2) n := by
  rw [quadraticGeometricTerm, pow_mul]

theorem quadratic_geometric_square_parameter (x : ℝ) : |x ^ 2| < 1 ↔ |x| < 1 := by
  rw [abs_of_nonneg (sq_nonneg x)]
  constructor
  · intro h
    exact abs_lt.mpr ⟨by nlinarith [sq_nonneg (x + 1)], by nlinarith [sq_nonneg (x - 1)]⟩
  · intro h
    have h' := abs_lt.mp h
    nlinarith [mul_pos (by linarith : 0 < 1 - x) (by linarith : 0 < 1 + x)]

theorem quadratic_geometric_source_hasSum (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * x ^ (2 * n))
      (x ^ 2 * (1 + x ^ 2) / (1 - x ^ 2) ^ 3) := by
  simpa only [quadratic_geometric_source_identity] using
    quadratic_geometric_hasSum (x ^ 2) ((quadratic_geometric_square_parameter x).mpr hx)

theorem quadratic_geometric_source_summable_iff (x : ℝ) :
    Summable (fun n : ℕ => (n : ℝ) ^ 2 * x ^ (2 * n)) ↔ |x| < 1 := by
  simp only [quadratic_geometric_source_identity, quadratic_geometric_summable_iff,
    quadratic_geometric_square_parameter]

theorem quadratic_geometric_source_partial_sums_converge_iff (x : ℝ) :
    (∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, (n : ℝ) ^ 2 * x ^ (2 * n))
      atTop (𝓝 L)) ↔ |x| < 1 := by
  simp only [quadratic_geometric_source_identity, quadratic_geometric_partial_sums_converge_iff,
    quadratic_geometric_square_parameter]

theorem quadratic_geometric_source_tail (x : ℝ) (hx : |x| < 1) (N : ℕ) :
    x ^ 2 * (1 + x ^ 2) / (1 - x ^ 2) ^ 3 -
        ∑ n ∈ Finset.range N, (n : ℝ) ^ 2 * x ^ (2 * n) =
      x ^ (2 * N) * ((N : ℝ) ^ 2 / (1 - x ^ 2) +
        2 * (N : ℝ) * x ^ 2 / (1 - x ^ 2) ^ 2 +
        x ^ 2 * (1 + x ^ 2) / (1 - x ^ 2) ^ 3) := by
  simpa only [quadratic_geometric_source_identity, pow_mul] using
    quadratic_geometric_tail (x ^ 2) ((quadratic_geometric_square_parameter x).mpr hx) N

theorem quadratic_geometric_source_uniform (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range N, (n : ℝ) ^ 2 * x ^ (2 * n))
      (fun x => ∑' n : ℕ, (n : ℝ) ^ 2 * x ^ (2 * n)) atTop (Set.Icc (-r) r) := by
  have hr' : |r ^ 2| < 1 := (quadratic_geometric_square_parameter r).mpr
    (by simpa only [abs_of_nonneg hr] using hr1)
  apply tendstoUniformlyOn_tsum_nat (quadratic_geometric_hasSum (r ^ 2) hr').summable
  intro n x hx
  rw [quadratic_geometric_source_identity]
  apply quadratic_geometric_majorant
  have h := pow_le_pow_left₀ (abs_nonneg x) (abs_le.mpr hx) 2
  simpa only [abs_pow] using h

theorem quadratic_geometric_source_uniform_absolute (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range N, |(n : ℝ) ^ 2 * x ^ (2 * n)|)
      (fun x => ∑' n : ℕ, |(n : ℝ) ^ 2 * x ^ (2 * n)|) atTop (Set.Icc (-r) r) := by
  have hr' : |r ^ 2| < 1 := (quadratic_geometric_square_parameter r).mpr
    (by simpa only [abs_of_nonneg hr] using hr1)
  apply tendstoUniformlyOn_tsum_nat (quadratic_geometric_hasSum (r ^ 2) hr').summable
  intro n x hx
  simp only [quadratic_geometric_source_identity, Real.norm_eq_abs, abs_abs]
  have h : |x ^ 2| ≤ r ^ 2 := by
    simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg x) (abs_le.mpr hx) 2
  exact quadratic_geometric_majorant (x ^ 2) (r ^ 2) h n

theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) :
    ∃ y, ∑' n : ℕ, (n^2 * x^(2 * n)) = y := by
  exact ⟨_, (quadratic_geometric_source_hasSum x
    (by simpa only [abs_of_pos hx.1] using hx.2)).tsum_eq⟩

#print axioms quadraticGeometricTerm
#print axioms quadratic_geometric_hasSum
#print axioms quadratic_geometric_norm
#print axioms quadratic_geometric_terms_vanish_iff
#print axioms quadratic_geometric_summable_iff
#print axioms quadratic_geometric_partial_sums_converge_iff
#print axioms quadratic_geometric_tail_hasSum
#print axioms quadratic_geometric_tail
#print axioms quadratic_geometric_majorant
#print axioms quadratic_geometric_uniform
#print axioms quadratic_geometric_uniform_absolute
#print axioms quadratic_geometric_source_identity
#print axioms quadratic_geometric_square_parameter
#print axioms quadratic_geometric_source_hasSum
#print axioms quadratic_geometric_source_summable_iff
#print axioms quadratic_geometric_source_partial_sums_converge_iff
#print axioms quadratic_geometric_source_tail
#print axioms quadratic_geometric_source_uniform
#print axioms quadratic_geometric_source_uniform_absolute
#print axioms solution
