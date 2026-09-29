-- Prove2me | solution 1 for lean_workbook_plus_75020
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T14:28:28.503412+00:00
-- url     : https://prove2.me/submissions/910a9d96-d466-4d53-a15b-7021bd4de0a2

import Mathlib.Tactic

theorem solution (n : ℕ) : n * (n - 1) / 2 = n.choose 2 := by
  rw [Nat.choose_two_right]
