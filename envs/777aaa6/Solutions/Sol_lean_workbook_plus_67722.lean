-- Prove2me | solution 1 for lean_workbook_plus_67722
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:36.511722+00:00
-- url     : https://prove2.me/submissions/411bb359-d9b5-4a03-8d1d-61e58f78b331

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (S : Set ℝ) (hS : S ⊆ Set.Icc 0 1) (hn : ∀ n : ℕ, (1 / n : ℝ) ∈ S) (hx : ∀ x ∈ S, ∀ n : ℕ, (x + 1 / n) / 2 ∈ S) : S ⊆ Set.Icc (0 : ℚ) 1 := by
  (intros; simp_all)
