-- Prove2me | solution 1 for lean_workbook_plus_80805
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:19:10.177635+00:00
-- url     : https://prove2.me/submissions/7d1fe6d1-1d08-4857-a433-31d7b8b9c163

import Mathlib

theorem solution (f : ℝ → ℝ) (hf : ∀ x, f x ≤ x)
    (hadd : ∀ x y, f (x + y) ≤ f x + f y) : ∀ x, f x = x := by
  have h00 := hadd 0 0
  simp only [add_zero] at h00
  have hz : f 0 = 0 := by linarith [hf 0]
  intro x
  have hx := hadd x (-x)
  simp only [add_neg_cancel] at hx
  linarith [hf x, hf (-x)]
