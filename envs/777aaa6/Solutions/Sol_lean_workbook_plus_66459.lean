-- Prove2me | solution 1 for lean_workbook_plus_66459
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:09:25.368156+00:00
-- url     : https://prove2.me/submissions/253b0031-a82c-4537-b1d7-f4b3f97400d8

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : ∃ f : ℝ → ℝ, f x = (x^3 + 8*x)/6 + (-(x - 2*Int.floor (x/2))^3 + 6*(x - 2*Int.floor (x/2))^2 - 8*(x - 2*Int.floor (x/2)))/6 := by
  exact ⟨fun x => (x^3 + 8*x)/6 + (-(x - 2*Int.floor (x/2))^3 + 6*(x - 2*Int.floor (x/2))^2 - 8*(x - 2*Int.floor (x/2)))/6, rfl⟩
