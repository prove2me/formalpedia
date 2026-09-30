-- Prove2me | solution 1 for lean_workbook_plus_44869
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:40:47.540662+00:00
-- url     : https://prove2.me/submissions/ac1685be-2682-4545-bf53-1766f0511de3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ¬ (∀ (f g : ℝ → ℝ), Continuous f → Continuous g →
    (∀ x, (f x) ^ 2 + (g x) ^ 2 = 1) →
    ∃ x ∈ Set.Icc (-1) 1, f x * g x = 1) := by
  intro h
  obtain ⟨x, hx, he⟩ := h (fun _ => 1) (fun _ => 0)
    continuous_const continuous_const (by intro x; norm_num)
  change (1 : ℝ) * 0 = 1 at he
  norm_num at he

#print axioms solution
