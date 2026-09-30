-- Prove2me | solution 1 for lean_workbook_plus_147
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:50.540994+00:00
-- url     : https://prove2.me/submissions/98192359-038e-4b2b-a7d0-755a68968b67

import Mathlib

theorem solution (f : ℝ → ℝ) (hf : ∀ x y : ℝ, f (x + y) = f (x - y)) :
    ∃ a : ℝ, ∀ x : ℝ, f x = a := by
  refine ⟨f 0, ?_⟩
  intro x
  have h := hf (x / 2) (x / 2)
  rw [show x / 2 + x / 2 = x by ring, sub_self] at h
  exact h
