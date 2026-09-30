-- Prove2me | solution 1 for lean_workbook_plus_82230
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:51:17.501954+00:00
-- url     : https://prove2.me/submissions/de2b76d4-fbf0-4b79-9ac8-34f040afeaa6

import Mathlib

theorem solution (a b c : ℝ) :
    a^2 + b^2 + c^2 = a * b + b * c + c * a ↔ a = b ∧ b = c := by
  constructor
  · intro h
    constructor
    · nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    · nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  · rintro ⟨rfl, rfl⟩
    ring
