-- Prove2me | solution 1 for lean_workbook_plus_8741
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:42:50.177435+00:00
-- url     : https://prove2.me/submissions/358d7b7e-30c7-4737-a4a6-9883fd9071eb

import Mathlib.Analysis.Complex.Basic

theorem solution (S E G : ℝ) : S / (E + G) = 30 → E + G = S / 30 := by
  intro h
  have hne : E + G ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h
    norm_num at h
  have hS : S = 30 * (E + G) := by
    field_simp at h
    linarith
  rw [hS]
  ring
