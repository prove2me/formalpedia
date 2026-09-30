-- Prove2me | solution 1 for lean_workbook_plus_189
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:49.737862+00:00
-- url     : https://prove2.me/submissions/e36d7202-fef8-47a0-a1bf-002a321505e3

import Mathlib

theorem solution (f : ℝ → ℝ)
    (hf : ∀ a v w : ℝ, f (a * v) = a * f v ∧ f (v + w) = f v + f w) :
    ∃ c : ℝ, ∀ x : ℝ, f x = c * x := by
  refine ⟨f 1, ?_⟩
  intro x
  simpa only [mul_one, mul_comm] using (hf x 1 0).1
