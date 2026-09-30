-- Prove2me | solution 1 for lean_workbook_plus_18688
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:27:01.723974+00:00
-- url     : https://prove2.me/submissions/46b54979-e5fd-444b-8424-770b5e6de773

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (n : ℕ) : ∃ (f : ℕ → ℝ), f n = 2 * a * f (n - 1) - b ^ 2 * f (n - 2) :=
  ⟨fun _ => 0, by simp⟩
