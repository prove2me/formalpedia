-- Prove2me | solution 1 for mme_dwz_table2_entropy_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T09:49:57.473735+00:00
-- url     : https://prove2.me/submissions/cd268257-f6be-4fc7-bf10-c3d01ddb4d53

import Definitions.Def_mme_dwz_square_data

open BigOperators Finset
open MME.DWZSquare

private noncomputable def certLogSeries (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1)

private theorem certLogMem
    (q x lo hi : ℝ) (n : ℕ)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hq : q = (1 + x) / (1 - x))
    (hlo : lo ≤ 2 * certLogSeries x n)
    (hhi : 2 * (certLogSeries x n +
      x ^ (2 * n + 1) / (1 - x ^ 2)) ≤ hi) :
    lo ≤ Real.log q ∧ Real.log q ≤ hi := by
  have hL := Real.sum_range_le_log_div hx0 hx1 n
  have hU := Real.log_div_le_sum_range_add hx0 hx1 n
  rw [← hq] at hL hU
  have hL' : certLogSeries x n ≤ 1 / 2 * Real.log q := by
    simpa [certLogSeries, Nat.cast_add, Nat.cast_mul] using hL
  have hU' : 1 / 2 * Real.log q ≤
      certLogSeries x n + x ^ (2 * n + 1) / (1 - x ^ 2) := by
    simpa [certLogSeries, Nat.cast_add, Nat.cast_mul] using hU
  constructor <;> nlinarith

private theorem certLogTwo :
    (69314718055 / 100000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (69314718057 / 100000000000 : ℝ) := by
  apply certLogMem 2 (1 / 3) _ _ 12 <;>
    norm_num [certLogSeries, sum_range_succ]

private theorem certScaled
    (q r x c eps : ℝ) (k n : ℕ)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hratio : r = (1 + x) / (1 - x))
    (hq : q = r / (2 : ℝ) ^ k)
    (hrpos : 0 < r)
    (hd : 0 ≤ c + k - eps)
    (hlo : (c + k - eps) * (69314718057 / 100000000000 : ℝ) ≤
      2 * certLogSeries x n)
    (hhi : 2 * (certLogSeries x n +
      x ^ (2 * n + 1) / (1 - x ^ 2)) ≤
      (c + k + eps) * (69314718055 / 100000000000 : ℝ)) :
    |Real.log q / Real.log 2 - c| ≤ eps := by
  have htwo := certLogTwo
  have htwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr := certLogMem r x
    (2 * certLogSeries x n)
    (2 * (certLogSeries x n + x ^ (2 * n + 1) / (1 - x ^ 2))) n
    hx0 hx1 hratio le_rfl le_rfl
  have hscaled : Real.log q = Real.log r - (k : ℝ) * Real.log 2 := by
    rw [hq, Real.log_div hrpos.ne'
      (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne', Real.log_pow]
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ htwoPos, hscaled]
    have hc : (c + k - eps) * Real.log 2 ≤
        (c + k - eps) * (69314718057 / 100000000000 : ℝ) :=
      mul_le_mul_of_nonneg_left htwo.2 hd
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ htwoPos, hscaled]
    have hc : (c + k + eps) * (69314718055 / 100000000000 : ℝ) ≤
        (c + k + eps) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_left htwo.1
      linarith
    nlinarith

private lemma cert0 :
    |Real.log (1043 / 5000000 : ℝ) / Real.log 2 -
      (-122269733 / 10000000 : ℝ)| ≤ 1 / 250000 := by
  apply certScaled
    (q := 1043 / 5000000) (r := 133504 / 78125)
    (x := 55379 / 211629) (c := -122269733 / 10000000)
    (eps := 1 / 250000) (k := 13) (n := 9) <;>
    norm_num [certLogSeries, sum_range_succ]

private lemma cert1 :
    |Real.log (24731 / 100000000 : ℝ) / Real.log 2 -
      (-59906959 / 5000000 : ℝ)| ≤ 1 / 250000 := by
  apply certScaled
    (q := 24731 / 100000000) (r := 395696 / 390625)
    (x := 5071 / 786321) (c := -59906959 / 5000000)
    (eps := 1 / 250000) (k := 12) (n := 9) <;>
    norm_num [certLogSeries, sum_range_succ]

private lemma cert3 :
    |Real.log (1211153 / 100000000 : ℝ) / Real.log 2 -
      (-63674751 / 10000000 : ℝ)| ≤ 1 / 250000 := by
  apply certScaled
    (q := 1211153 / 100000000) (r := 1211153 / 781250)
    (x := 429903 / 1992403) (c := -63674751 / 10000000)
    (eps := 1 / 250000) (k := 7) (n := 9) <;>
    norm_num [certLogSeries, sum_range_succ]

private lemma cert4 :
    |Real.log (666659 / 50000000 : ℝ) / Real.log 2 -
      (-6228837 / 1000000 : ℝ)| ≤ 1 / 250000 := by
  apply certScaled
    (q := 666659 / 50000000) (r := 666659 / 390625)
    (x := 138017 / 528642) (c := -6228837 / 1000000)
    (eps := 1 / 250000) (k := 7) (n := 9) <;>
    norm_num [certLogSeries, sum_range_succ]

private lemma cert6 :
    |Real.log (625879 / 50000000 : ℝ) / Real.log 2 -
      (-63198987 / 10000000 : ℝ)| ≤ 1 / 250000 := by
  apply certScaled
    (q := 625879 / 50000000) (r := 625879 / 390625)
    (x := 117627 / 508252) (c := -63198987 / 10000000)
    (eps := 1 / 250000) (k := 7) (n := 9) <;>
    norm_num [certLogSeries, sum_range_succ]

private lemma cert9 :
    |Real.log (2073389 / 20000000 : ℝ) / Real.log 2 -
      (-8174839 / 2500000 : ℝ)| ≤ 1 / 250000 := by
  apply certScaled
    (q := 2073389 / 20000000) (r := 2073389 / 1250000)
    (x := 823389 / 3323389) (c := -8174839 / 2500000)
    (eps := 1 / 250000) (k := 4) (n := 9) <;>
    norm_num [certLogSeries, sum_range_succ]

private lemma cert11 :
    |Real.log (10045791 / 100000000 : ℝ) / Real.log 2 -
      (-8288351 / 2500000 : ℝ)| ≤ 1 / 250000 := by
  apply certScaled
    (q := 10045791 / 100000000) (r := 10045791 / 6250000)
    (x := 3795791 / 16295791) (c := -8288351 / 2500000)
    (eps := 1 / 250000) (k := 4) (n := 9) <;>
    norm_num [certLogSeries, sum_range_succ]

private lemma cert12 :
    |Real.log (20088623 / 100000000 : ℝ) / Real.log 2 -
      (-23155529 / 10000000 : ℝ)| ≤ 1 / 250000 := by
  apply certScaled
    (q := 20088623 / 100000000) (r := 20088623 / 12500000)
    (x := 7588623 / 32588623) (c := -23155529 / 10000000)
    (eps := 1 / 250000) (k := 3) (n := 9) <;>
    norm_num [certLogSeries, sum_range_succ]

private lemma cert13 :
    |Real.log (10367229 / 50000000 : ℝ) / Real.log 2 -
      (-283737 / 125000 : ℝ)| ≤ 1 / 250000 := by
  apply certScaled
    (q := 10367229 / 50000000) (r := 10367229 / 6250000)
    (x := 4117229 / 16617229) (c := -283737 / 125000)
    (eps := 1 / 250000) (k := 3) (n := 9) <;>
    norm_num [certLogSeries, sum_range_succ]

theorem solution (s : Fin 15) :
    |Real.log (alpha s) / Real.log 2 -
      (entropyLambdaZero + entropyLambdaX (shapeX s) +
        entropyLambdaY (shapeY s) + entropyLambdaZ (shapeZ s))| ≤
      entropyEpsilon := by
  fin_cases s <;>
    simp [alpha, shapeX, shapeY, shapeZ, entropyLambdaZero,
      entropyLambdaX, entropyLambdaY, entropyLambdaZ, entropyEpsilon,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four] <;>
    norm_num
  · convert cert0 using 1 <;> ring
  · convert cert1 using 1 <;> ring
  · convert cert1 using 1 <;> ring
  · convert cert3 using 1 <;> ring
  · convert cert4 using 1 <;> ring
  · convert cert3 using 1 <;> ring
  · convert cert6 using 1 <;> ring
  · convert cert4 using 1 <;> ring
  · convert cert6 using 1 <;> ring
  · convert cert9 using 1 <;> ring
  · convert cert9 using 1 <;> ring
  · convert cert11 using 1 <;> ring
  · convert cert12 using 1 <;> ring
  · convert cert13 using 1 <;> ring
  · convert cert13 using 1 <;> ring
