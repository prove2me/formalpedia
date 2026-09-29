-- Prove2me | solution 1 for lean_workbook_plus_6074
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:52.646128+00:00
-- url     : https://prove2.me/submissions/f2f45dfc-a21c-4943-8479-2ed745e20302

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (h : ∀ i j k : ℕ, 1 ≤ i ∧ i ≤ j ∧ j ≤ k ∧ k ≤ 100 → a k ^ 2 ≤ a i ^ 2 + a j ^ 2) : ∀ i j k : ℕ, 1 ≤ i ∧ i ≤ j ∧ j ≤ k ∧ k ≤ 100 → a k ^ 2 ≤ a i ^ 2 + a j ^ 2 := by
  (intros; simp_all)
