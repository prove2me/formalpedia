-- Prove2me | solution 1 for lean_workbook_plus_13094
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:01:12.712552+00:00
-- url     : https://prove2.me/submissions/43d4cdb8-3d23-4101-9cf7-ee94ccf5f72e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (f : ℝ → ℝ) :
    (∀ x y, (x + y) * (f x - f y) = f (x ^ 2) - f (y ^ 2)) ↔
      ∃ a b : ℝ, ∀ x, f x = a * x + b := by
  constructor
  · intro hf
    refine ⟨f 1 - f 0, f 0, ?_⟩
    intro x
    have h0 := hf x 0
    have h1 := hf x 1
    simp only [zero_pow (by decide : 2 ≠ 0), add_zero] at h0
    simp only [one_pow] at h1
    nlinarith only [h0, h1]
  · rintro ⟨a, b, hab⟩ x y
    simp only [hab]
    ring
