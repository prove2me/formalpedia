-- Prove2me | solution 1 for lean_workbook_plus_57735
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:37:33.351655+00:00
-- url     : https://prove2.me/submissions/80fab9b3-c97c-4ebb-90ae-6a312885d1bb

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (f : ℝ → ℝ) :
    (∀ x y, f (x ^ 2 - y) = f y - f x ^ 2) ↔ ∀ x, f x = 0 := by
  constructor
  · intro h
    have h00 := h 0 0
    norm_num only [zero_pow, sub_zero] at h00
    have hz : f 0 = 0 := sq_eq_zero_iff.mp (sub_eq_self.mp h00.symm)
    intro x
    have hx0 := h x 0
    have hxx := h x (x^2)
    rw [sub_zero, hz] at hx0
    rw [sub_self, hz] at hxx
    apply sq_eq_zero_iff.mp
    linarith only [hx0, hxx]
  · intro h x y
    rw [h (x^2 - y), h y, h x]
    norm_num
