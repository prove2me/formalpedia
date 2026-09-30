-- Prove2me | solution 1 for lean_workbook_plus_67677
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:23:16.067544+00:00
-- url     : https://prove2.me/submissions/6524a052-bf34-45bb-a1d0-22e6af324d9d

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℕ) (n : ℕ) (hn: x = 5^n*2^(n-1) ∧ y = 10^n ∧ z = 5^(2*n)*2^(2*n-1)) : x*y*z = 10^n * (5^n * 2^(n-1)) * (5^(2*n) * 2^(2*n-1)) := by
  obtain ⟨rfl, rfl, rfl⟩ := hn
  ring
