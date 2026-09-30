-- Prove2me | solution 1 for lean_workbook_plus_82040
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:28:29.144828+00:00
-- url     : https://prove2.me/submissions/492ec0aa-1668-4d86-81d0-08e2a46a6790

import Mathlib

theorem solution (x y : ℝ) :
    (2*y = -x + 3 ∧ -y = 5*x + 1) ↔ (x = -5/9 ∧ y = 16/9) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    norm_num
