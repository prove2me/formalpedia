-- Prove2me | solution 1 for lean_workbook_plus_19839
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:07:14.202144+00:00
-- url     : https://prove2.me/submissions/697c730e-63df-4891-8891-c7df111a61a4

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℝ) (ha : a ∈ Set.Icc 2 3) (hb : b ∈ Set.Icc 2 3) (hc : c ∈ Set.Icc 2 3) (hd : d ∈ Set.Icc 2 3) : (2 / 3 ≤ (a * (c - d) + 3 * d) / (b * (d - c) + 3 * c) ∧ (a * (c - d) + 3 * d) / (b * (d - c) + 3 * c) ≤ 3 / 2) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨hd1, hd2⟩ := hd
  have hD : 0 < b * (d - c) + 3 * c := by nlinarith [mul_nonneg (sub_nonneg.2 hb1) (sub_nonneg.2 hc1), mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 hc1)]
  constructor
  · rw [le_div_iff₀ hD]
    nlinarith [mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hd1), mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 hd1),
      mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hc1), mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 hc1),
      mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hd2), mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 hd2),
      mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hc2), mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 hc2)]
  · rw [div_le_iff₀ hD]
    nlinarith [mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hd1), mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 hd1),
      mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hc1), mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 hc1),
      mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hd2), mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 hd2),
      mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hc2), mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 hc2)]
