-- Prove2me | solution 1 for mme_dwz_square_component_log_rate_23747_gt_442868
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T10:08:57.240106+00:00
-- url     : https://prove2.me/submissions/71e7c25e-5a25-401b-9e46-4b92a277e0b3

import Definitions.Def_mme_dwz_square_data
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic


open Finset

namespace MME.DWZNumeric

/-!
Small, fully rigorous interval certificates for logarithms of rational
numbers.  The expansion used here is

  log ((1+x)/(1-x)) = 2 * sum_{i >= 0} x^(2i+1)/(2i+1).

`Real.sum_range_le_log_div` and `Real.log_div_le_sum_range_add` supply the
one-sided remainder bounds; all applications below reduce to rational
arithmetic with `norm_num`.
-/

noncomputable def logSeries (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1)

theorem log_mem_Icc_of_ratio
    (q x lo hi : ℝ) (n : ℕ)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hq : q = (1 + x) / (1 - x))
    (hlo : lo ≤ 2 * logSeries x n)
    (hhi : 2 * (logSeries x n + x ^ (2 * n + 1) / (1 - x ^ 2)) ≤ hi) :
    lo ≤ Real.log q ∧ Real.log q ≤ hi := by
  have hL := Real.sum_range_le_log_div hx0 hx1 n
  have hU := Real.log_div_le_sum_range_add hx0 hx1 n
  rw [← hq] at hL hU
  have hL' : logSeries x n ≤ 1 / 2 * Real.log q := by
    simpa [logSeries, Nat.cast_add, Nat.cast_mul] using hL
  have hU' : 1 / 2 * Real.log q ≤
      logSeries x n + x ^ (2 * n + 1) / (1 - x ^ 2) := by
    simpa [logSeries, Nat.cast_add, Nat.cast_mul] using hU
  constructor <;> nlinarith

/- A tight common interval for `log 2`. -/
theorem log_two_mem :
    (69314718055 / 100000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (69314718057 / 100000000000 : ℝ) := by
  apply log_mem_Icc_of_ratio 2 (1 / 3) _ _ 12 <;>
    norm_num [logSeries, sum_range_succ]

theorem abs_log_div_log_two_sub_le_of_scaled
    (q r x c eps : ℝ) (k n : ℕ)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hratio : r = (1 + x) / (1 - x))
    (hq : q = r / (2 : ℝ) ^ k)
    (hrpos : 0 < r)
    (hd : 0 ≤ c + k - eps)
    (hlo : (c + k - eps) * (69314718057 / 100000000000 : ℝ) ≤
      2 * logSeries x n)
    (hhi : 2 * (logSeries x n + x ^ (2 * n + 1) / (1 - x ^ 2)) ≤
      (c + k + eps) * (69314718055 / 100000000000 : ℝ)) :
    |Real.log q / Real.log 2 - c| ≤ eps := by
  have htwo := log_two_mem
  have htwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr := log_mem_Icc_of_ratio r x
    (2 * logSeries x n)
    (2 * (logSeries x n + x ^ (2 * n + 1) / (1 - x ^ 2))) n
    hx0 hx1 hratio le_rfl le_rfl
  have hscaled : Real.log q = Real.log r - (k : ℝ) * Real.log 2 := by
    rw [hq, Real.log_div hrpos.ne' (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne',
      Real.log_pow]
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ htwoPos]
    rw [hscaled]
    have hcoef : (c + k - eps) * Real.log 2 ≤
        (c + k - eps) * (69314718057 / 100000000000 : ℝ) :=
      mul_le_mul_of_nonneg_left htwo.2 hd
    push_cast
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ htwoPos]
    rw [hscaled]
    have hcoef : (c + k + eps) * (69314718055 / 100000000000 : ℝ) ≤
        (c + k + eps) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_left htwo.1
      linarith
    push_cast
    nlinarith

end MME.DWZNumeric

open BigOperators Finset

namespace MME.DWZNumeric

open MME.DWZSquare

private lemma log_three_halves :
    |Real.log (3 / 2 : ℝ) / Real.log 2 -
      (5849625 / 10000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 3 / 2) (r := 3 / 2) (x := 1 / 5)
    (c := 5849625 / 10000000) (eps := 1 / 10000000)
    (k := 0) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma log_nineteen_sixteen :
    |Real.log (19 / 16 : ℝ) / Real.log 2 -
      (24792751 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 19 / 16) (r := 19 / 16) (x := 3 / 35)
    (c := 24792751 / 100000000) (eps := 1 / 10000000)
    (k := 0) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma log_seventy_three_seventy_one :
    |Real.log (73 / 71 : ℝ) / Real.log 2 -
      (4007744 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 73 / 71) (r := 73 / 71) (x := 1 / 72)
    (c := 4007744 / 100000000) (eps := 1 / 10000000)
    (k := 0) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma log_a :
    |Real.log (3477403 / 100000000 : ℝ) / Real.log 2 -
      (-30286537 / 6250000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 3477403 / 100000000) (r := 3477403 / 3125000)
    (x := 352403 / 6602403) (c := -30286537 / 6250000)
    (eps := 1 / 10000000) (k := 5) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma log_am :
    |Real.log (46522597 / 50000000 : ℝ) / Real.log 2 -
      (-5199823 / 50000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 46522597 / 50000000) (r := 46522597 / 25000000)
    (x := 21522597 / 71522597) (c := -5199823 / 50000000)
    (eps := 1 / 10000000) (k := 1) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma log_b :
    |Real.log (4203 / 20000000 : ℝ) / Real.log 2 -
      (-305407323 / 25000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 4203 / 20000000) (r := 134496 / 78125)
    (x := 56371 / 212621) (c := -305407323 / 25000000)
    (eps := 1 / 10000000) (k := 13) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma log_bm :
    |Real.log (9995797 / 10000000 : ℝ) / Real.log 2 -
      (-60649 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 9995797 / 10000000) (r := 9995797 / 5000000)
    (x := 4995797 / 14995797) (c := -60649 / 100000000)
    (eps := 1 / 10000000) (k := 1) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

theorem log_six_ratio_lower :
    (25849624 / 10000000 : ℝ) ≤ Real.log 6 / Real.log 2 := by
  have h := (abs_le.mp log_three_halves).1
  have h2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hid : Real.log 6 / Real.log 2 =
      2 + Real.log (3 / 2 : ℝ) / Real.log 2 := by
    rw [show (6 : ℝ) = (3 / 2) * 2 ^ 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    field_simp
    ring
  rw [hid]
  linarith

theorem log_twelve_ratio_lower :
    (35849624 / 10000000 : ℝ) ≤ Real.log 12 / Real.log 2 := by
  have h := (abs_le.mp log_three_halves).1
  have hid : Real.log 12 / Real.log 2 =
      3 + Real.log (3 / 2 : ℝ) / Real.log 2 := by
    rw [show (12 : ℝ) = (3 / 2) * 2 ^ 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    ring
  rw [hid]
  linarith

theorem log_thirty_eight_ratio_lower :
    (524792741 / 100000000 : ℝ) ≤ Real.log 38 / Real.log 2 := by
  have h := (abs_le.mp log_nineteen_sixteen).1
  have hid : Real.log 38 / Real.log 2 =
      5 + Real.log (19 / 16 : ℝ) / Real.log 2 := by
    rw [show (38 : ℝ) = (19 / 16) * 2 ^ 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    ring
  rw [hid]
  linarith

theorem log_seventy_three_ratio_lower :
    (4007734 / 100000000 : ℝ) ≤
      Real.log (73 / 71) / Real.log 2 := by
  have h := (abs_le.mp log_seventy_three_seventy_one).1
  linarith

theorem six_rpow_tau3_lt_seventy_one :
    Real.rpow 6 (3 * (23747 / 30000 : ℝ)) < 71 := by
  have hexp : (3 * (23747 / 30000 : ℝ)) < 19 / 8 := by norm_num
  have hmono := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 6) hexp
  have hp19 : (6 : ℝ) ^ (19 / 8 : ℝ) < 71 := by
    apply (pow_lt_pow_iff_left₀
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 6) (19 / 8))
      (by norm_num : (0 : ℝ) ≤ 71)
      (by norm_num : (8 : ℕ) ≠ 0)).mp
    have heq : ((6 : ℝ) ^ (19 / 8 : ℝ)) ^ (8 : ℕ) = (6 : ℝ) ^ (19 : ℕ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
      norm_num
    rw [heq]
    norm_num
  exact hmono.trans hp19

theorem component_class_3_8_gt :
    (283773 / 100000 : ℝ) <
      Real.log (componentBase (23747 / 30000) 3) / Real.log 2 := by
  have h := log_twelve_ratio_lower
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  simp [componentBase]
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 12)]
  field_simp [hlog2] at h ⊢
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem component_class_11_gt :
    (415408 / 100000 : ℝ) <
      Real.log (componentBase (23747 / 30000) 11) / Real.log 2 := by
  have h := log_thirty_eight_ratio_lower
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  simp [componentBase]
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 38)]
  field_simp [hlog2] at h ⊢
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem component_class_9_10_gt :
    (415109 / 100000 : ℝ) <
      Real.log (componentBase (23747 / 30000) 9) / Real.log 2 := by
  have h6 := log_six_ratio_lower
  have ha := (abs_le.mp log_a).2
  have hm := (abs_le.mp log_am).2
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  have ha0 : (0 : ℝ) < splitA := by norm_num [splitA]
  have hm0 : (0 : ℝ) < 1 - 2 * splitA := by norm_num [splitA]
  have hden0 : 0 <
      Real.rpow splitA (2 * splitA) *
        Real.rpow (1 - 2 * splitA) (1 - 2 * splitA) := by
    exact mul_pos (Real.rpow_pos_of_pos ha0 _) (Real.rpow_pos_of_pos hm0 _)
  have hnum0 : 0 < Real.rpow 6 (2 * (1 - 2 * splitA)) := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hbase0 : 0 <
      (6 : ℝ) ^ (2 * (1 - 2 * splitA)) /
        (splitA ^ (2 * splitA) *
          (1 - 2 * splitA) ^ (1 - 2 * splitA)) := by
    simpa only [Real.rpow_eq_pow] using div_pos hnum0 hden0
  have hnum0' : 0 < (6 : ℝ) ^ (2 * (1 - 2 * splitA)) := by
    simpa only [Real.rpow_eq_pow] using hnum0
  have hden0' : 0 <
      splitA ^ (2 * splitA) *
        (1 - 2 * splitA) ^ (1 - 2 * splitA) := by
    simpa only [Real.rpow_eq_pow] using hden0
  have hpa0 : 0 < splitA ^ (2 * splitA) :=
    Real.rpow_pos_of_pos ha0 _
  have hpm0 : 0 < (1 - 2 * splitA) ^ (1 - 2 * splitA) :=
    Real.rpow_pos_of_pos hm0 _
  simp [componentBase]
  change (415109 / 100000 : ℝ) <
    Real.log (Real.rpow
      (Real.rpow 6 (2 * (1 - 2 * splitA)) /
        (Real.rpow splitA (2 * splitA) *
          Real.rpow (1 - 2 * splitA) (1 - 2 * splitA)))
      (23747 / 30000)) / Real.log 2
  simp only [Real.rpow_eq_pow]
  rw [Real.log_rpow hbase0]
  rw [Real.log_div hnum0'.ne' hden0'.ne',
    Real.log_mul hpa0.ne' hpm0.ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 6),
    Real.log_rpow ha0, Real.log_rpow hm0]
  have hid :
      (23747 / 30000 : ℝ) *
          ((2 * (1 - 2 * splitA)) * Real.log 6 -
            ((2 * splitA) * Real.log splitA +
              (1 - 2 * splitA) * Real.log (1 - 2 * splitA))) /
          Real.log 2 =
        (23747 / 30000 : ℝ) *
          (2 * (1 - 2 * splitA) * (Real.log 6 / Real.log 2) -
            2 * splitA * (Real.log splitA / Real.log 2) -
            (1 - 2 * splitA) *
              (Real.log (1 - 2 * splitA) / Real.log 2)) := by
    field_simp [hlog2]
    ring
  rw [hid]
  norm_num [splitA] at ha hm ⊢
  nlinarith

theorem component_class_12_gt :
    (476006 / 100000 : ℝ) <
      Real.log (componentBase (23747 / 30000) 12) / Real.log 2 := by
  have h6 := log_six_ratio_lower
  have hb := (abs_le.mp log_b).2
  have hm := (abs_le.mp log_bm).2
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  have hb0 : (0 : ℝ) < splitB := by norm_num [splitB]
  have hm0 : (0 : ℝ) < 1 - 2 * splitB := by norm_num [splitB]
  have hpm0 : 0 < (1 - 2 * splitB) ^ (1 - 2 * splitB) :=
    Real.rpow_pos_of_pos hm0 _
  have hpb0 : 0 < splitB ^ (2 * splitB) :=
    Real.rpow_pos_of_pos hb0 _
  have hden0 : 0 <
      (1 - 2 * splitB) ^ (1 - 2 * splitB) *
        splitB ^ (2 * splitB) := mul_pos hpm0 hpb0
  have hfrac0 : 0 < (4 : ℝ) /
      ((1 - 2 * splitB) ^ (1 - 2 * splitB) *
        splitB ^ (2 * splitB)) := div_pos (by norm_num) hden0
  have hleft0 : 0 <
      ((4 : ℝ) /
        ((1 - 2 * splitB) ^ (1 - 2 * splitB) *
          splitB ^ (2 * splitB))) ^ (3 : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos hfrac0 _
  have hright0 : 0 <
      (6 : ℝ) ^ ((2 - 2 * splitB) * (23747 / 30000 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  simp [componentBase]
  rw [Real.log_mul hleft0.ne' hright0.ne',
    Real.log_rpow hfrac0,
    Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hden0.ne',
    Real.log_mul hpm0.ne' hpb0.ne',
    Real.log_rpow hm0, Real.log_rpow hb0,
    Real.log_rpow (by norm_num : (0 : ℝ) < 6)]
  have hlog4 : Real.log (4 : ℝ) / Real.log 2 = 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    field_simp [hlog2]
    ring
  have hlog4' : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    field_simp [hlog2] at hlog4
    linarith
  have hid :
      (((3 : ℝ)⁻¹ *
            (Real.log 4 -
              ((1 - 2 * splitB) * Real.log (1 - 2 * splitB) +
                (2 * splitB) * Real.log splitB)) +
          ((2 - 2 * splitB) * (23747 / 30000 : ℝ)) * Real.log 6) /
          Real.log 2) =
        (1 / 3 : ℝ) *
            (2 - (1 - 2 * splitB) *
                (Real.log (1 - 2 * splitB) / Real.log 2) -
              2 * splitB * (Real.log splitB / Real.log 2)) +
          ((2 - 2 * splitB) * (23747 / 30000 : ℝ)) *
            (Real.log 6 / Real.log 2) := by
    rw [hlog4']
    field_simp [hlog2]
    ring
  rw [hid]
  norm_num [splitB] at hb hm ⊢
  nlinarith

theorem component_class_13_14_gt :
    (477236 / 100000 : ℝ) <
      Real.log (componentBase (23747 / 30000) 13) / Real.log 2 := by
  let tau : ℝ := 23747 / 30000
  let P : ℝ := (6 : ℝ) ^ (3 * tau)
  have hP0 : 0 < P := Real.rpow_pos_of_pos (by norm_num) _
  have hP71 : P < 71 := by
    simpa only [P, tau, Real.rpow_eq_pow] using
      six_rpow_tau3_lt_seventy_one
  have hsmall : (2 / 71 : ℝ) * P < 2 := by
    have h := mul_lt_mul_of_pos_left hP71 (by norm_num : (0 : ℝ) < 2 / 71)
    norm_num at h ⊢
    exact h
  have hprod : (73 / 71 : ℝ) * P < P + 2 := by
    have hid : (73 / 71 : ℝ) * P = P + (2 / 71) * P := by ring
    rw [hid]
    linarith
  have hleft0 : 0 < (73 / 71 : ℝ) * P :=
    mul_pos (by norm_num) hP0
  have hlog :
      Real.log ((73 / 71 : ℝ) * P) < Real.log (P + 2) :=
    Real.log_lt_log hleft0 hprod
  have hlogleft :
      Real.log ((73 / 71 : ℝ) * P) =
        Real.log (73 / 71) + (3 * tau) * Real.log 6 := by
    rw [Real.log_mul (by norm_num : (73 / 71 : ℝ) ≠ 0) hP0.ne']
    change Real.log (73 / 71) + Real.log ((6 : ℝ) ^ (3 * tau)) = _
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 6)]
  rw [hlogleft] at hlog
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogratio0 := (div_lt_div_iff_of_pos_right hlog2pos).2 hlog
  have hdist :
      (Real.log (73 / 71) + (3 * tau) * Real.log 6) / Real.log 2 =
        Real.log (73 / 71) / Real.log 2 +
          (3 * tau) * (Real.log 6 / Real.log 2) := by
    field_simp [hlog2pos.ne']
  rw [hdist] at hlogratio0
  have h6 := log_six_ratio_lower
  have h73 := log_seventy_three_ratio_lower
  have hA0 : 0 < (2 : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hB0 : 0 < (6 : ℝ) ^ tau :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hC0 : 0 < (P + 2) ^ (3 : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (by linarith) _
  have hB0' : 0 < (6 : ℝ) ^ (23747 / 30000 : ℝ) := by
    simpa only [tau] using hB0
  have hC0' : 0 <
      ((6 : ℝ) ^ (3 * (23747 / 30000 : ℝ)) + 2) ^ (3 : ℝ)⁻¹ := by
    simpa only [P, tau] using hC0
  simp [componentBase]
  rw [Real.log_mul (mul_pos hA0 hB0').ne' hC0'.ne',
    Real.log_mul hA0.ne' hB0'.ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_rpow (by norm_num : (0 : ℝ) < 6),
    Real.log_rpow (by
      have : 0 < (6 : ℝ) ^ (3 * (23747 / 30000 : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      linarith)]
  change (477236 / 100000 : ℝ) <
    (((2 / 3 : ℝ) * Real.log 2 + tau * Real.log 6 +
        (3 : ℝ)⁻¹ * Real.log (P + 2)) / Real.log 2)
  have hid :
      (((2 / 3 : ℝ) * Real.log 2 + tau * Real.log 6 +
          (3 : ℝ)⁻¹ * Real.log (P + 2)) / Real.log 2) =
        (2 / 3 : ℝ) + tau * (Real.log 6 / Real.log 2) +
          (1 / 3 : ℝ) * (Real.log (P + 2) / Real.log 2) := by
    field_simp [hlog2pos.ne']
  rw [hid]
  norm_num [tau] at hlogratio0 h6 h73 ⊢
  nlinarith

theorem componentLogRate_gt_442868 :
    (442868 / 100000 : ℝ) <
      componentLogRate (23747 / 30000) := by
  have h3 := component_class_3_8_gt
  have h9 := component_class_9_10_gt
  have h11 := component_class_11_gt
  have h12 := component_class_12_gt
  have h13 := component_class_13_14_gt
  rw [componentLogRate]
  simp [alpha, componentBase, Fin.sum_univ_succ] at h3 h9 h11 h12 h13 ⊢
  nlinarith

end MME.DWZNumeric

open MME.DWZSquare

theorem solution :
    (442868 / 100000 : ℝ) < componentLogRate (23747 / 30000) :=
  MME.DWZNumeric.componentLogRate_gt_442868
