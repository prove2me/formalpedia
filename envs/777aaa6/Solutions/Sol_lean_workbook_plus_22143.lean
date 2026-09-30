-- Prove2me | solution 1 for lean_workbook_plus_22143
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:22:44.207627+00:00
-- url     : https://prove2.me/submissions/ca1f1b37-2940-4d9c-9848-8fe04e882e1a

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hxy : 0 < x ∧ x ≤ y) (hyz : y ≤ z ∧ z ≤ 3) (h : y * z ≤ 6) (h' : x * y * z ≤ 6) : x + y + z ≤ 6 := by
  obtain ⟨hx, hxy⟩ := hxy
  obtain ⟨hyz, hz3⟩ := hyz
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) (sub_nonneg.2 hyz), mul_nonneg (sub_nonneg.2 hyz) (sub_nonneg.2 hz3),
    mul_nonneg (sub_nonneg.2 hxy) (sub_nonneg.2 hz3), mul_pos hx (by linarith : (0:ℝ) < y), mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hz3),
    mul_nonneg (sub_nonneg.2 h') (sub_nonneg.2 hz3), mul_nonneg (sub_nonneg.2 h) hx.le]
