-- Prove2me | solution 1 for lean_workbook_plus_21880
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:51:52.726381+00:00
-- url     : https://prove2.me/submissions/e337ec08-ab5a-494a-baa5-86415b157d1e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (f : ℝ → ℝ) :
    (∀ x y z : ℝ, (x*y+y*z+z*x=0 →
      f (x-y) + f (y-z) - f (z-x) = f (x+y+z))) ↔
    ∃ c : ℝ, ∀ x : ℝ, f x = c := by
  constructor
  · intro h
    refine ⟨f 0, ?_⟩
    intro x
    have hh := h 0 (-x) 0 (by ring)
    simp only [zero_sub, sub_zero, sub_self, zero_add, add_zero, neg_neg] at hh
    linarith only [hh]
  · rintro ⟨c, h⟩ x y z _
    simp only [h]
    ring
