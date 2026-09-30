-- Prove2me | solution 1 for lean_workbook_plus_11736
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:51:11.372017+00:00
-- url     : https://prove2.me/submissions/ab42d51a-5a1f-4897-a050-17c5295de5cd

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open Filter
open scoped Topology

theorem reciprocal_quadratic_positive_summable (a : ℝ) :
    Summable (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2 + a ^ 2)) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  apply hs.of_nonneg_of_le (fun n => by positivity)
  intro n
  exact one_div_le_one_div_of_le (by positivity) (le_add_of_nonneg_right (sq_nonneg a))

theorem imaginary_parameter_not_integer {a : ℝ} (ha : 0 < a) :
    (a : ℂ) * Complex.I ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨m, hm⟩
  have hi := congrArg Complex.im hm
  simp only [Complex.intCast_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero] at hi
  linarith

theorem imaginary_cotTerm_identity {a : ℝ} (ha : 0 < a) (n : ℕ) :
    cotTerm ((a : ℂ) * Complex.I) n =
      (-2 * (a : ℂ) * Complex.I) *
        ((1 / (((n : ℝ) + 1) ^ 2 + a ^ 2) : ℝ) : ℂ) := by
  rw [cotTerm_identity (imaginary_parameter_not_integer ha)]
  have hden : ((a : ℂ) * Complex.I + (n + 1)) *
      ((a : ℂ) * Complex.I - (n + 1)) =
      -(((((n : ℝ) + 1) ^ 2 + a ^ 2) : ℝ) : ℂ) := by
    push_cast
    calc
      _ = (a : ℂ) ^ 2 * Complex.I ^ 2 - (n + 1) ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [hden, div_neg]
  push_cast
  ring

theorem reciprocal_quadratic_series_value {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2 + a ^ 2)) =
      (Real.pi * Real.cosh (Real.pi * a) / Real.sinh (Real.pi * a) - 1 / a) / (2 * a) := by
  let S : ℝ := ∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ 2 + a ^ 2)
  have hs := (reciprocal_quadratic_positive_summable a).hasSum
  have hc : HasSum (fun n => cotTerm ((a : ℂ) * Complex.I) n)
      ((-2 * (a : ℂ) * Complex.I) * (S : ℂ)) := by
    apply ((Complex.hasSum_ofReal.mpr hs).mul_left (-2 * (a : ℂ) * Complex.I)).congr_fun
    exact imaginary_cotTerm_identity ha
  have h := cot_series_rep' (imaginary_parameter_not_integer ha)
  change (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * ((a : ℂ) * Complex.I)) -
    1 / ((a : ℂ) * Complex.I) = ∑' n : ℕ, cotTerm ((a : ℂ) * Complex.I) n at h
  rw [hc.tsum_eq] at h
  have harg : (Real.pi : ℂ) * ((a : ℂ) * Complex.I) =
      ((Real.pi * a : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [harg, Complex.cot, Complex.cos_mul_I, Complex.sin_mul_I,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh] at h
  simp only [div_mul_eq_div_div, Complex.div_I] at h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.neg_im, Complex.neg_re, Complex.mul_im,
    Complex.mul_re, Complex.div_ofReal_im,
    Complex.div_ofReal_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
    mul_zero, zero_mul, zero_add, add_zero, mul_one, zero_div] at hi
  change S = _
  apply (eq_div_iff (mul_ne_zero (by norm_num) ha.ne')).mpr
  rw [mul_div_assoc]
  linarith

theorem reciprocal_quadratic_series_hasSum {a : ℝ} (ha : 0 < a) :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2 + a ^ 2))
      ((Real.pi * Real.cosh (Real.pi * a) / Real.sinh (Real.pi * a) - 1 / a) / (2 * a)) := by
  rw [← reciprocal_quadratic_series_value ha]
  exact (reciprocal_quadratic_positive_summable a).hasSum

theorem reciprocal_square_plus_one_positive_value :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2 + 1))
      ((Real.pi * Real.cosh Real.pi / Real.sinh Real.pi - 1) / 2) := by
  simpa only [one_pow, mul_one, div_one] using
    reciprocal_quadratic_series_hasSum (a := 1) (by norm_num)

theorem reciprocal_square_plus_one_all_summable :
    Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2 + 1)) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using reciprocal_square_plus_one_positive_value.summable

theorem reciprocal_square_plus_one_all_value :
    (∑' n : ℕ, 1 / ((n : ℝ) ^ 2 + 1)) =
      (Real.pi * Real.cosh Real.pi / Real.sinh Real.pi + 1) / 2 := by
  have h := reciprocal_square_plus_one_all_summable.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
    zero_add, div_one, Nat.cast_add, Nat.cast_one] at h
  rw [reciprocal_square_plus_one_positive_value.tsum_eq] at h
  linarith

theorem solution (f : ℕ → ℝ) (hf : ∀ n, f n = 1 / (n ^ 2 + 1)) :
    ∃ l, ∑' n : ℕ, f n = l := by
  refine ⟨(Real.pi * Real.cosh Real.pi / Real.sinh Real.pi + 1) / 2, ?_⟩
  simp_rw [hf]
  exact reciprocal_square_plus_one_all_value

#print axioms reciprocal_quadratic_positive_summable
#print axioms imaginary_parameter_not_integer
#print axioms imaginary_cotTerm_identity
#print axioms reciprocal_quadratic_series_value
#print axioms reciprocal_quadratic_series_hasSum
#print axioms reciprocal_square_plus_one_positive_value
#print axioms reciprocal_square_plus_one_all_summable
#print axioms reciprocal_square_plus_one_all_value
#print axioms solution
