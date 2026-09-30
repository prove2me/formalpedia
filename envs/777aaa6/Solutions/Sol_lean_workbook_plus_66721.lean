-- Prove2me | solution 1 for lean_workbook_plus_66721
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:40:04.221743+00:00
-- url     : https://prove2.me/submissions/87022c35-d978-465d-94af-5224386f8d96

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (hn : n % 3 = 0) (a : ℕ → ℕ) (ha : a = fun i ↦ if i % 3 = 0 then n else if i % 3 = 1 then 1 else 1) : ∃ k : ℕ, a k = n ∧ ∃ l : ℕ, a l = 1 ∧ ∃ m : ℕ, a m = 1 := by
  subst ha
  exact ⟨0, by simp, 1, by simp, 1, by simp⟩
