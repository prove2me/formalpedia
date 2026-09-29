-- Prove2me | solution 1 for mme_dwz_square_retained_log_rate_gt_157133
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T10:03:02.033336+00:00
-- url     : https://prove2.me/submissions/a95c91e7-cda4-465b-ae63-578119ef2e36

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_table2_entropy_potential
import Theorems.Thm_mme_modern_entropyBits_additive_certificate

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

theorem xMarginal_eq :
    mme_modern_marginal shapeX alpha =
      ![12957007 / 100000000, 5410749 / 12500000,
        20573597 / 50000000, 646269 / 25000000,
        24731 / 100000000] := by
  funext i
  unfold mme_modern_marginal
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun s : Fin 15 ↦ shapeX s = i)) (by simp) alpha]
  rw [Finset.sum_filter]
  fin_cases i <;>
    simp [shapeX, alpha, Fin.sum_univ_succ] <;>
    (try split_ifs) <;> norm_num at *

private lemma xlog_0 :
    |Real.log (12957007 / 100000000 : ℝ) / Real.log 2 -
      (-294819559 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 12957007 / 100000000) (r := 12957007 / 12500000)
    (x := 457007 / 25457007) (c := -294819559 / 100000000)
    (eps := 1 / 10000000) (k := 3) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma xlog_1 :
    |Real.log (5410749 / 12500000 : ℝ) / Real.log 2 -
      (-120802787 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 5410749 / 12500000) (r := 5410749 / 3125000)
    (x := 2285749 / 8535749) (c := -120802787 / 100000000)
    (eps := 1 / 10000000) (k := 2) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma xlog_2 :
    |Real.log (20573597 / 50000000 : ℝ) / Real.log 2 -
      (-32028351 / 25000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 20573597 / 50000000) (r := 20573597 / 12500000)
    (x := 8073597 / 33073597) (c := -32028351 / 25000000)
    (eps := 1 / 10000000) (k := 2) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma xlog_3 :
    |Real.log (646269 / 25000000 : ℝ) / Real.log 2 -
      (-527364949 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 646269 / 25000000) (r := 646269 / 390625)
    (x := 127822 / 518447) (c := -527364949 / 100000000)
    (eps := 1 / 10000000) (k := 6) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma xlog_4 :
    |Real.log (24731 / 100000000 : ℝ) / Real.log 2 -
      (-59906959 / 5000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 24731 / 100000000) (r := 395696 / 390625)
    (x := 5071 / 786321) (c := -59906959 / 5000000)
    (eps := 1 / 10000000) (k := 12) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

theorem entropy_x_gt_157134 :
    (157134 / 100000 : ℝ) <
      mme_modern_entropyBits (mme_modern_marginal shapeX alpha) := by
  rw [xMarginal_eq]
  have h0 := (abs_le.mp xlog_0).2
  have h1 := (abs_le.mp xlog_1).2
  have h2 := (abs_le.mp xlog_2).2
  have h3 := (abs_le.mp xlog_3).2
  have h4 := (abs_le.mp xlog_4).2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [sub_le_iff_le_add, div_le_iff₀ hlog2pos] at h0 h1 h2 h3 h4
  simp [mme_modern_entropyBits, Fin.sum_univ_succ,
    Real.negMulLog_def, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.cons_val_fin_one]
  rw [lt_div_iff₀ hlog2pos]
  nlinarith

theorem maxSameMarginalEntropy_le :
    maxSameMarginalEntropy ≤
      mme_modern_entropyBits alpha + 2 * entropyEpsilon := by
  apply csSup_le
  · refine ⟨mme_modern_entropyBits alpha, ?_⟩
    refine ⟨alpha, fun s ↦ (alpha_pos s).le, alpha_sum, ?_, ?_, ?_, rfl⟩ <;>
      intro i <;> rfl
  · intro h hh
    rcases hh with ⟨p, hp, hpSum, hmX, hmY, hmZ, rfl⟩
    exact mme_modern_entropyBits_additive_certificate
      shapeX shapeY shapeZ p alpha entropyLambdaZero
      entropyLambdaX entropyLambdaY entropyLambdaZ entropyEpsilon
      hp alpha_pos hpSum alpha_sum hmX hmY hmZ
      (by norm_num [entropyEpsilon]) mme_dwz_table2_entropy_potential

theorem retained_first_branch_gt_157133 :
    (157133 / 100000 : ℝ) <
      mme_modern_entropyBits alpha +
        mme_modern_entropyBits (mme_modern_marginal shapeX alpha) -
        maxSameMarginalEntropy := by
  have hx := entropy_x_gt_157134
  have hm := maxSameMarginalEntropy_le
  norm_num [entropyEpsilon] at hm ⊢
  linarith

end MME.DWZNumeric

open BigOperators Finset

namespace MME.DWZNumeric

open MME.DWZSquare

private theorem entropy_half_left :
    mme_modern_entropyBits (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) = 1 := by
  have h2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  simp [mme_modern_entropyBits, Fin.sum_univ_succ, Real.negMulLog_def,
    Real.log_div, h2]
  field_simp
  norm_num

private theorem entropy_half_right :
    mme_modern_entropyBits (![0, 1 / 2, 1 / 2] : Fin 3 → ℝ) = 1 := by
  have h2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  simp [mme_modern_entropyBits, Fin.sum_univ_succ, Real.negMulLog_def,
    Real.log_div, h2]
  field_simp
  norm_num

private theorem entropy_unit_left :
    mme_modern_entropyBits (![1, 0, 0] : Fin 3 → ℝ) = 0 := by
  simp [mme_modern_entropyBits, Fin.sum_univ_succ]

private theorem entropy_unit_right :
    mme_modern_entropyBits (![0, 0, 1] : Fin 3 → ℝ) = 0 := by
  simp [mme_modern_entropyBits, Fin.sum_univ_succ]

theorem boundary_entropy_eq :
    (∑ s : Fin 15,
      if shapeX s = 0 ∨ shapeY s = 0 then
        alpha s * mme_modern_entropyBits (zSplit s)
      else 0) =
      (5088942 / 100000000 : ℝ) +
        (10366945 / 50000000 : ℝ) *
          mme_modern_entropyBits
            (![splitA, 1 - 2 * splitA, splitA] : Fin 3 → ℝ) := by
  have ehl : mme_modern_entropyBits (![2⁻¹, 2⁻¹, 0] : Fin 3 → ℝ) = 1 := by
    convert entropy_half_left using 1 <;> norm_num
  have ehr : mme_modern_entropyBits (![0, 2⁻¹, 2⁻¹] : Fin 3 → ℝ) = 1 := by
    convert entropy_half_right using 1 <;> norm_num
  simp [Fin.sum_univ_succ, shapeX, shapeY, alpha, zSplit, shapeZ,
    splitA]
  rw [entropy_unit_left, entropy_unit_right, ehl, ehr]
  ring

private theorem plusSplit_zero :
    plusSplit 0 = (![1, 0, 0] : Fin 3 → ℝ) := by
  funext r
  fin_cases r <;>
    simp [plusSplit, plusMass, shapeX, shapeY, shapeZ, alpha, zSplit,
      Fin.sum_univ_succ] <;> norm_num <;> rfl

private theorem plusSplit_one :
    plusSplit 1 = (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) := by
  funext r
  fin_cases r <;>
    simp [plusSplit, plusMass, shapeX, shapeY, shapeZ, alpha, zSplit,
      Fin.sum_univ_succ] <;> norm_num

private theorem plusSplit_two :
    plusSplit 2 = (![splitB, 1 - 2 * splitB, splitB] : Fin 3 → ℝ) := by
  funext r
  fin_cases r <;>
    simp [plusSplit, plusMass, shapeX, shapeY, shapeZ, alpha, zSplit,
      splitB, Fin.sum_univ_succ] <;> norm_num

theorem interior_entropy_eq :
    (∑ k : Fin 5, plusMass k * mme_modern_entropyBits (plusSplit k)) =
      (10367229 / 25000000 : ℝ) +
        (20088623 / 100000000 : ℝ) *
          mme_modern_entropyBits
            (![splitB, 1 - 2 * splitB, splitB] : Fin 3 → ℝ) := by
  simp [Fin.sum_univ_succ, plusMass, plusSplit, shapeX, shapeY, shapeZ,
    alpha, zSplit, splitA, splitB, entropy_half_left]
  rw [plusSplit_zero, plusSplit_one, plusSplit_two,
    entropy_unit_left, entropy_half_left]
  simp [splitB]
  norm_num

theorem retained_second_branch_eq :
    mme_modern_entropyBits (mme_modern_marginal shapeZ alpha) - logAlphaP =
      mme_modern_entropyBits gamma -
        (5088942 / 100000000 : ℝ) -
        (10366945 / 50000000 : ℝ) *
          mme_modern_entropyBits
            (![splitA, 1 - 2 * splitA, splitA] : Fin 3 → ℝ) -
        (10367229 / 25000000 : ℝ) -
        (20088623 / 100000000 : ℝ) *
          mme_modern_entropyBits
            (![splitB, 1 - 2 * splitB, splitB] : Fin 3 → ℝ) := by
  rw [logAlphaP, boundary_entropy_eq, interior_entropy_eq]
  ring

theorem gamma_eq_table : gamma = fun r ↦
    (![
      ![12598769 / 100000000, 344809 / 1562500,
        14504450740003 / 2000000000000000],
      ![344809 / 1562500, 393720679259997 / 1000000000000000,
        1211153 / 100000000],
      ![14504450740003 / 2000000000000000, 1211153 / 100000000,
        1043 / 5000000]
    ] : Fin 3 → Fin 3 → ℝ) r.1 r.2 := by
  funext r
  rcases r with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [gamma, Fin.sum_univ_succ, shapeZ, alpha, zSplit, splitA, splitB] <;>
    norm_num <;> ring

private lemma glog_00 :
    |Real.log (12598769 / 100000000 : ℝ) / Real.log 2 -
      (-74716133 / 25000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 12598769 / 100000000) (r := 12598769 / 12500000)
    (x := 98769 / 25098769) (c := -74716133 / 25000000)
    (eps := 1 / 10000000) (k := 3) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma glog_01 :
    |Real.log (344809 / 1562500 : ℝ) / Real.log 2 -
      (-43599737 / 20000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 344809 / 1562500) (r := 689618 / 390625)
    (x := 298993 / 1080243) (c := -43599737 / 20000000)
    (eps := 1 / 10000000) (k := 3) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma glog_02 :
    |Real.log (14504450740003 / 2000000000000000 : ℝ) / Real.log 2 -
      (-710736053 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 14504450740003 / 2000000000000000)
    (r := 14504450740003 / 7812500000000)
    (x := 6691950740003 / 22316950740003)
    (c := -710736053 / 100000000)
    (eps := 1 / 10000000) (k := 8) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma glog_11 :
    |Real.log (393720679259997 / 1000000000000000 : ℝ) / Real.log 2 -
      (-134475561 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 393720679259997 / 1000000000000000)
    (r := 393720679259997 / 250000000000000)
    (x := 143720679259997 / 643720679259997)
    (c := -134475561 / 100000000)
    (eps := 1 / 10000000) (k := 2) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma glog_12 :
    |Real.log (1211153 / 100000000 : ℝ) / Real.log 2 -
      (-318373753 / 50000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1211153 / 100000000) (r := 1211153 / 781250)
    (x := 429903 / 1992403) (c := -318373753 / 50000000)
    (eps := 1 / 10000000) (k := 7) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma glog_22 :
    |Real.log (1043 / 5000000 : ℝ) / Real.log 2 -
      (-611348661 / 50000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 1043 / 5000000) (r := 133504 / 78125)
    (x := 55379 / 211629) (c := -611348661 / 50000000)
    (eps := 1 / 10000000) (k := 13) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

theorem entropy_gamma_gt_21280183 :
    (21280183 / 10000000 : ℝ) < mme_modern_entropyBits gamma := by
  rw [gamma_eq_table]
  have h00 := (abs_le.mp glog_00).2
  have h01 := (abs_le.mp glog_01).2
  have h02 := (abs_le.mp glog_02).2
  have h11 := (abs_le.mp glog_11).2
  have h12 := (abs_le.mp glog_12).2
  have h22 := (abs_le.mp glog_22).2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [sub_le_iff_le_add, div_le_iff₀ hlog2pos] at h00 h01 h02 h11 h12 h22
  simp [mme_modern_entropyBits, Fintype.sum_prod_type, Fin.sum_univ_succ,
    Real.negMulLog_def]
  rw [lt_div_iff₀ hlog2pos]
  nlinarith

private lemma alog_small :
    |Real.log (3477403 / 100000000 : ℝ) / Real.log 2 -
      (-30286537 / 6250000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 3477403 / 100000000) (r := 3477403 / 3125000)
    (x := 352403 / 6602403) (c := -30286537 / 6250000)
    (eps := 1 / 10000000) (k := 5) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma alog_middle :
    |Real.log (46522597 / 50000000 : ℝ) / Real.log 2 -
      (-5199823 / 50000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 46522597 / 50000000) (r := 46522597 / 25000000)
    (x := 21522597 / 71522597) (c := -5199823 / 50000000)
    (eps := 1 / 10000000) (k := 1) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma blog_small :
    |Real.log (4203 / 20000000 : ℝ) / Real.log 2 -
      (-305407323 / 25000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 4203 / 20000000) (r := 134496 / 78125)
    (x := 56371 / 212621) (c := -305407323 / 25000000)
    (eps := 1 / 10000000) (k := 13) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

private lemma blog_middle :
    |Real.log (9995797 / 10000000 : ℝ) / Real.log 2 -
      (-60649 / 100000000 : ℝ)| ≤ 1 / 10000000 := by
  apply abs_log_div_log_two_sub_le_of_scaled
    (q := 9995797 / 10000000) (r := 9995797 / 5000000)
    (x := 4995797 / 14995797) (c := -60649 / 100000000)
    (eps := 1 / 10000000) (k := 1) (n := 9) <;>
    norm_num [logSeries, sum_range_succ]

theorem entropy_splitA_lt :
    mme_modern_entropyBits
        (![splitA, 1 - 2 * splitA, splitA] : Fin 3 → ℝ) <
      (54223 / 125000 : ℝ) := by
  have hs := (abs_le.mp alog_small).1
  have hm := (abs_le.mp alog_middle).1
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_sub_iff_add_le, le_div_iff₀ hlog2pos] at hs hm
  simp [mme_modern_entropyBits, splitA, Fin.sum_univ_succ,
    Real.negMulLog_def]
  rw [div_lt_iff₀ hlog2pos]
  nlinarith

theorem entropy_splitB_lt :
    mme_modern_entropyBits
        (![splitB, 1 - 2 * splitB, splitB] : Fin 3 → ℝ) <
      (5741 / 1000000 : ℝ) := by
  have hs := (abs_le.mp blog_small).1
  have hm := (abs_le.mp blog_middle).1
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_sub_iff_add_le, le_div_iff₀ hlog2pos] at hs hm
  simp [mme_modern_entropyBits, splitB, Fin.sum_univ_succ,
    Real.negMulLog_def]
  rw [div_lt_iff₀ hlog2pos]
  nlinarith

theorem retained_second_branch_gt_157133 :
    (157133 / 100000 : ℝ) <
      mme_modern_entropyBits (mme_modern_marginal shapeZ alpha) - logAlphaP := by
  rw [retained_second_branch_eq]
  have hg := entropy_gamma_gt_21280183
  have ha := entropy_splitA_lt
  have hb := entropy_splitB_lt
  nlinarith

theorem retainedLogRate_gt_157133 :
    (157133 / 100000 : ℝ) < retainedLogRate := by
  rw [retainedLogRate, lt_min_iff]
  exact ⟨retained_first_branch_gt_157133, retained_second_branch_gt_157133⟩

end MME.DWZNumeric

theorem solution :
    (157133 / 100000 : ℝ) < MME.DWZSquare.retainedLogRate :=
  MME.DWZNumeric.retainedLogRate_gt_157133
