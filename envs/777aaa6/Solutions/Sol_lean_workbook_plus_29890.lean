-- Prove2me | solution 1 for lean_workbook_plus_29890
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:41:45.302541+00:00
-- url     : https://prove2.me/submissions/60d9e552-fa44-4386-ae7f-b50dec5f8003

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h : c ≥ b ∧ b ≥ a ∧ a ≥ 0) :
    (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c := by
  obtain ⟨hcb, hba, ha⟩ := h
  have hb : b ≥ 0 := le_trans ha hba
  have hc : c ≥ 0 := le_trans hb hcb
  nlinarith [mul_nonneg (mul_nonneg ha (sub_nonneg.2 hcb)) (sub_nonneg.2 hba),
    mul_nonneg (mul_nonneg hb (sub_nonneg.2 hcb)) (sub_nonneg.2 hba),
    mul_nonneg (mul_nonneg hc (sub_nonneg.2 hcb)) (sub_nonneg.2 hba),
    mul_nonneg (mul_nonneg ha (sub_nonneg.2 hcb)) (sub_nonneg.2 hcb),
    mul_nonneg (mul_nonneg hb (sub_nonneg.2 hcb)) (sub_nonneg.2 hcb),
    mul_nonneg (mul_nonneg hc (sub_nonneg.2 hcb)) (sub_nonneg.2 hcb),
    mul_nonneg (mul_nonneg ha (sub_nonneg.2 hba)) (sub_nonneg.2 hba),
    mul_nonneg (mul_nonneg hb (sub_nonneg.2 hba)) (sub_nonneg.2 hba),
    mul_nonneg (mul_nonneg hc (sub_nonneg.2 hba)) (sub_nonneg.2 hba),
    mul_nonneg (mul_nonneg ha hb) (sub_nonneg.2 hcb),
    mul_nonneg (mul_nonneg ha hb) (sub_nonneg.2 hba),
    mul_nonneg (mul_nonneg ha hc) (sub_nonneg.2 hcb),
    mul_nonneg (mul_nonneg ha hc) (sub_nonneg.2 hba),
    mul_nonneg (mul_nonneg hb hc) (sub_nonneg.2 hcb),
    mul_nonneg (mul_nonneg hb hc) (sub_nonneg.2 hba),
    mul_nonneg (mul_nonneg ha hb) hc]
