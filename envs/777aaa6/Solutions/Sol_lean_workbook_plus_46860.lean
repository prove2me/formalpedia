-- Prove2me | solution 1 for lean_workbook_plus_46860
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:24:39.573711+00:00
-- url     : https://prove2.me/submissions/31c1617f-6dae-41b2-b634-7afbeb28c1b7

import Mathlib.Analysis.Complex.Basic

/-- Cauchy–Schwarz step: if `1/t1 + 1/t2 + 1/t3 = 4/Q` with all quantities positive,
then `4 (t1 + t2 + t3) ≥ 9 Q`. -/
theorem aux_cs (t1 t2 t3 Q : ℝ) (h1 : 0 < t1) (h2 : 0 < t2) (h3 : 0 < t3) (hQ : 0 < Q)
    (key : 1 / t1 + 1 / t2 + 1 / t3 = 4 / Q) : 4 * (t1 + t2 + t3) ≥ 9 * Q := by
  have hE : 0 < t1 * t2 + t2 * t3 + t3 * t1 := by positivity
  rw [div_add_div _ _ h1.ne' h2.ne', div_add_div _ _ (by positivity) h3.ne',
    div_eq_div_iff (by positivity) hQ.ne'] at key
  have key' : (t1 * t2 + t2 * t3 + t3 * t1) * Q = 4 * (t1 * t2 * t3) := by
    linear_combination key
  have amgm : (t1 + t2 + t3) * (t1 * t2 + t2 * t3 + t3 * t1) ≥ 9 * (t1 * t2 * t3) := by
    nlinarith [mul_nonneg h1.le (sq_nonneg (t2 - t3)), mul_nonneg h2.le (sq_nonneg (t1 - t3)),
      mul_nonneg h3.le (sq_nonneg (t1 - t2))]
  nlinarith [amgm, key', hE, mul_pos hE hQ]

/-- AM–GM for three nonnegative reals. -/
theorem aux_amgm (U V W : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) :
    27 * (U * V * W) ≤ (U + V + W) ^ 3 := by
  nlinarith [mul_nonneg hV (sq_nonneg (U - W)), mul_nonneg hU (sq_nonneg (V - W)),
    mul_nonneg hW (sq_nonneg (U - V)),
    mul_nonneg (add_nonneg (add_nonneg hU hV) hW)
      (add_nonneg (add_nonneg (sq_nonneg (U - V)) (sq_nonneg (V - W))) (sq_nonneg (W - U)))]

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a * b * c ≠ 0) (h : (a * b / (1 + a + b)) + (b * c / (1 + b + c)) + (c * a / (1 + c + a)) = 1) : 1 + a + b + c ≥ 4 * a * b * c := by
  have ha' : 0 < a := lt_of_le_of_ne ha (by rintro rfl; simp at habc)
  have hb' : 0 < b := lt_of_le_of_ne hb (by rintro rfl; simp at habc)
  have hc' : 0 < c := lt_of_le_of_ne hc (by rintro rfl; simp at habc)
  -- Step 1: rewrite the constraint as Σ 1/((a+1)(b+c+1)) = 4/((a+1)(b+1)(c+1)).
  have key : 1 / ((a + 1) * (b + c + 1)) + 1 / ((b + 1) * (c + a + 1)) + 1 / ((c + 1) * (a + b + 1))
      = 4 / ((a + 1) * (b + 1) * (c + 1)) := by
    have e1 : 1 / ((a + 1) * (b + c + 1)) = (1 + b * c / (1 + b + c)) / ((a + 1) * (b + 1) * (c + 1)) := by
      field_simp; ring
    have e2 : 1 / ((b + 1) * (c + a + 1)) = (1 + c * a / (1 + c + a)) / ((a + 1) * (b + 1) * (c + 1)) := by
      field_simp; ring
    have e3 : 1 / ((c + 1) * (a + b + 1)) = (1 + a * b / (1 + a + b)) / ((a + 1) * (b + 1) * (c + 1)) := by
      field_simp; ring
    rw [e1, e2, e3, ← add_div, ← add_div]
    congr 1
    linarith [h]
  -- Step 2: Cauchy–Schwarz gives 3 Q ≥ 4 σ, i.e. 3(a+b+c) + 3 ≥ 9abc + (ab+bc+ca).
  have step1 := aux_cs _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity) key
  have step1' : 3 * (a + b + c) + 3 ≥ 9 * (a * b * c) + (a * b + b * c + c * a) := by
    nlinarith [step1]
  -- Step 3: AM–GM for U = (a+1)bc, V = (b+1)ca, W = (c+1)ab.
  have amgm := aux_amgm ((a + 1) * b * c) ((b + 1) * c * a) ((c + 1) * a * b)
    (by positivity) (by positivity) (by positivity)
  have hσ : (a + 1) * b * c + (b + 1) * c * a + (c + 1) * a * b
      = 3 * (a * b * c) + (a * b + b * c + c * a) := by ring
  have hUVW : ((a + 1) * b * c) * ((b + 1) * c * a) * ((c + 1) * a * b)
      = (a * b * c) ^ 2 * ((a + 1) * (b + 1) * (c + 1)) := by ring
  rw [hσ, hUVW] at amgm
  have hm : 0 < a * b * c := by positivity
  have hσpos : 0 < 3 * (a * b * c) + (a * b + b * c + c * a) := by positivity
  have h3Q : 3 * ((a + 1) * (b + 1) * (c + 1)) ≥ 4 * (3 * (a * b * c) + (a * b + b * c + c * a)) := by
    nlinarith [step1']
  -- Step 4: σ³ ≥ 27 m² Q ≥ 36 m² σ, hence σ² ≥ 36 m², hence σ ≥ 6 m, i.e. ab+bc+ca ≥ 3abc.
  have hσ3 : (3 * (a * b * c) + (a * b + b * c + c * a)) ^ 3
      ≥ 36 * (a * b * c) ^ 2 * (3 * (a * b * c) + (a * b + b * c + c * a)) := by
    nlinarith [amgm, h3Q, mul_nonneg (sq_nonneg (a * b * c)) (sub_nonneg.2 h3Q)]
  have hσ2 : (3 * (a * b * c) + (a * b + b * c + c * a)) ^ 2 ≥ 36 * (a * b * c) ^ 2 := by
    nlinarith [hσ3, hσpos]
  have hσ6 : 3 * (a * b * c) + (a * b + b * c + c * a) ≥ 6 * (a * b * c) := by
    nlinarith [hσ2, hσpos, hm]
  -- Conclusion.
  nlinarith [step1', hσ6]
