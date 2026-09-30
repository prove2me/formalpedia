-- Prove2me | solution 1 for lean_workbook_plus_32045
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:12:10.506272+00:00
-- url     : https://prove2.me/submissions/5d7f2394-cdd9-4edf-8896-d265cfea7a74

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h₁ : a * (1/b) = 1) (h₂ : b * (1/c) = 1) : c * (1/a) = 1 := by
  have hb : b ≠ 0 := by
    rintro rfl
    simp at h₁
  have hc : c ≠ 0 := by
    rintro rfl
    simp at h₂
  have hab : a = b := by
    field_simp at h₁
    linarith
  have hbc : b = c := by
    field_simp at h₂
    linarith
  subst hab
  subst hbc
  field_simp
