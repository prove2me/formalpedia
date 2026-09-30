-- Prove2me | solution 1 for lean_workbook_plus_75408
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:25:05.250317+00:00
-- url     : https://prove2.me/submissions/6d32210a-24ae-41e2-9b3f-f405c6e7725e

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℤ) (h : a+b+c ∣ a^2 + b^2 + c^2) : ∃ n : ℕ, a+b+c ∣ a^n + b^n + c^n := by
  exact ⟨2, h⟩
