-- Prove2me | solution 1 for lean_workbook_plus_5193
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:53:54.087489+00:00
-- url     : https://prove2.me/submissions/00da6f7a-195d-4a7a-9bd8-b3b29455c0d7

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (f : ℝ → ℝ) :
    (∀ x y, f (x + y) + f (x * y) = f (x^2) + f (y^2)) ↔
      ∃ l : ℝ, ∀ x, f x = l := by
  constructor
  · intro hf
    refine ⟨f 1, ?_⟩
    intro x
    have h0 := hf (x - 1) 0
    have h1 := hf (x - 1) 1
    simp only [add_zero, mul_zero, zero_pow (by decide : 2 ≠ 0)] at h0
    simp only [sub_add_cancel, mul_one, one_pow] at h1
    linarith
  · rintro ⟨l, hl⟩ x y
    simp only [hl]
