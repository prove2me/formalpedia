-- Prove2me | solution 1 for lean_workbook_plus_34023
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:15:06.79234+00:00
-- url     : https://prove2.me/submissions/b598087a-8d2c-4413-93b0-bb6c3a816b13

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (hn : 0 < n) : ∃ k : Fin 3, ¬ ∃ a : ℚ, (k : ℝ) = √(n + k) := by
  refine ⟨0, ?_⟩
  rintro ⟨a, ha⟩
  simp at ha
  have : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  linarith
