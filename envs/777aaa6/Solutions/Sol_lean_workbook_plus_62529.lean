-- Prove2me | solution 1 for lean_workbook_plus_62529
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:01:13.760152+00:00
-- url     : https://prove2.me/submissions/ac0aa9c4-cb05-4651-8ded-625f07d0e9ac

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (f : ℝ → ℝ) :
    (∀ x y, (x + y) * (f x - f y) = (x - y) * (f x + f y)) ↔
      ∃ c : ℝ, ∀ x : ℝ, f x = c * x := by
  constructor
  · intro hf
    refine ⟨f 1, ?_⟩
    intro x
    nlinarith only [hf x 1]
  · rintro ⟨c, hc⟩ x y
    simp only [hc]
    ring
