-- Prove2me | solution 1 for lean_workbook_plus_81133
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:51:16.030722+00:00
-- url     : https://prove2.me/submissions/8a16e7c3-606a-4da7-8ef9-94ce38f82ce5

import Mathlib

theorem solution (f : ℝ → ℝ)
    (hf : ∀ x y, f ((x + y) / 3) = (f x + f y) / 2) :
    ∀ x y, f (x + y) - f 0 = f x - f 0 + (f y - f 0) := by
  intro x y
  have h := hf (x + y) 0
  simp only [add_zero] at h
  linarith [hf x y]
