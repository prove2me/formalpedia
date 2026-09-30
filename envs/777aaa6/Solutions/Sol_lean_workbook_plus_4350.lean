-- Prove2me | solution 1 for lean_workbook_plus_4350
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:13:18.485199+00:00
-- url     : https://prove2.me/submissions/f1405750-f0d7-479d-87a6-9816b423c3a7

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (u v : ℝ) (h₁ : v > u) (h₂ : u > 1) (h₃ : f v = 1) (h₄ : f (f u) = -1) : ∃ u v, v > u ∧ u > 1 ∧ f v = 1 ∧ f (f u) = -1 :=
  ⟨u, v, h₁, h₂, h₃, h₄⟩
