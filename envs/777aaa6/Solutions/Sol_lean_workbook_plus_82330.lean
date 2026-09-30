-- Prove2me | solution 1 for lean_workbook_plus_82330
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:28:52.421911+00:00
-- url     : https://prove2.me/submissions/ef38f0ac-d496-4188-b9d1-5f0951fb784e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) :
    (∀ x y, f (x - f y) = 1 - x - y) ↔ ∀ x, f x = 1 / 2 - x := by
  constructor
  · intro h
    have hzero := h (f 0) 0
    simp only [sub_self, sub_zero] at hzero
    have hf0 : f 0 = 1 / 2 := by linarith
    intro x
    have hx := h (f x) x
    simp only [sub_self] at hx
    linarith
  · intro h x y
    simp only [h]
    ring
