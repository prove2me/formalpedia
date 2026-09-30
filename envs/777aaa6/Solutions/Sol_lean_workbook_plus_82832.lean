-- Prove2me | solution 1 for lean_workbook_plus_82832
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:03:09.991713+00:00
-- url     : https://prove2.me/submissions/94a67f37-9744-4a5b-8cd0-f26fe3eac995

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (h : ℝ → ℝ) (hcont : Continuous h) (h₀ : h 0 = 0) (x : ℝ) :
    ∃ f : ℝ → ℝ, Continuous f ∧ ∀ y ≤ 0, f y = -y ∧ ∀ y > 0, f y = y - h y := by
  refine ⟨fun y => -y + 2 * max y 0 - h (max y 0), ?_, ?_⟩
  · fun_prop
  · intro y hy
    constructor
    · simp [max_eq_right hy, h₀]
    · intro z hz
      simp only [max_eq_left hz.le]
      ring

#print axioms solution
