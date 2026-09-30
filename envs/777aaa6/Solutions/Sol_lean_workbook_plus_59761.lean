-- Prove2me | solution 1 for lean_workbook_plus_59761
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:34:08.151389+00:00
-- url     : https://prove2.me/submissions/3854c7e8-f817-43c5-9e35-3c174cf6ec8c

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 1 ≤ a ∧ a ≤ 3) (hb : 1 ≤ b ∧ b ≤ 3) (hc : 1 ≤ c ∧ c ≤ 3) : 3 / a + 45 / (a + b + c) ≥ 16 / (a + b) := by
  obtain ⟨ha1, ha3⟩ := ha
  obtain ⟨hb1, hb3⟩ := hb
  obtain ⟨hc1, hc3⟩ := hc
  have hapos : 0 < a := by linarith
  have habpos : 0 < a + b := by linarith
  have habcpos : 0 < a + b + c := by linarith
  rw [ge_iff_le, div_add_div _ _ hapos.ne' habcpos.ne', div_le_div_iff₀ habpos (mul_pos hapos habcpos)]
  nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1), mul_nonneg (sub_nonneg.mpr ha3) (sub_nonneg.mpr hb3),
    mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1), mul_nonneg (sub_nonneg.mpr ha3) (sub_nonneg.mpr hc3),
    mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc1), mul_nonneg (sub_nonneg.mpr hb3) (sub_nonneg.mpr hc3),
    mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr ha3), mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hb3),
    mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hc3)]
