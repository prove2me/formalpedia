-- Prove2me | solution 1 for lean_workbook_plus_15851
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:49:00.188192+00:00
-- url     : https://prove2.me/submissions/f651180d-60e6-4eb0-a12f-9ce87968978f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

private theorem product_iff_identity (f : ℝ → ℝ) :
    (∀ x y, (x+f y)*(f x+y) = x*f x+y*f y+2*y*f x) ↔ ∀ x, f x = x := by
  constructor
  · intro h x
    have hs : (f x-x)^2 = 0 := by nlinarith only [h x x]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · intro h x y
    rw [h x, h y]
    ring

theorem solution (f : ℝ → ℝ) (hf1 : ∀ x, f (f x) = x)
    (hf2 : ∀ x y, (x+f y)*(f x+y) = x*f x+y*f y+2*y*f x) :
    ∃ h : ℝ, ∀ x, f x = h*x := by
  refine ⟨1, ?_⟩
  simpa only [one_mul] using (product_iff_identity f).mp hf2
