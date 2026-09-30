-- Prove2me | solution 1 for lean_workbook_plus_38236
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:24:09.667948+00:00
-- url     : https://prove2.me/submissions/e24d7bbe-c5b0-4447-bc17-f0745d8fc133

import Mathlib.Analysis.Complex.Basic

theorem solution (A : Type*) [Ring A] (hA : ∀ a : A, a ^ 2 = 0) (hA' : ∀ n : ℕ, ∀ a : A, n * a = 0 → a = 0) (a b c : A) : a * b * c = 0 := by
  exact hA' 0 (a * b * c) (by simp)
