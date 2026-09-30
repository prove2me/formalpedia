-- Prove2me | solution 1 for lean_workbook_plus_64602
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:02:05.127168+00:00
-- url     : https://prove2.me/submissions/9ac7ebca-9fa3-4545-beeb-eb69ce286e8c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a^2+b^2-a*b = c^2) : (a-c)*(b-c) ≤ 0 := by
  rcases le_total a b with h | h
  · have h1 : a^2 ≤ c^2 := by
      nlinarith only [hab, mul_nonneg (le_of_lt hb) (sub_nonneg.mpr h)]
    have h2 : c^2 ≤ b^2 := by
      nlinarith only [hab, mul_nonneg (le_of_lt ha) (sub_nonneg.mpr h)]
    have hac := (sq_le_sq₀ (le_of_lt ha) (le_of_lt hc)).mp h1
    have hcb := (sq_le_sq₀ (le_of_lt hc) (le_of_lt hb)).mp h2
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hac) (sub_nonneg.mpr hcb)
  · have h1 : b^2 ≤ c^2 := by
      nlinarith only [hab, mul_nonneg (le_of_lt ha) (sub_nonneg.mpr h)]
    have h2 : c^2 ≤ a^2 := by
      nlinarith only [hab, mul_nonneg (le_of_lt hb) (sub_nonneg.mpr h)]
    have hbc := (sq_le_sq₀ (le_of_lt hb) (le_of_lt hc)).mp h1
    have hca := (sq_le_sq₀ (le_of_lt hc) (le_of_lt ha)).mp h2
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hca) (sub_nonpos.mpr hbc)
