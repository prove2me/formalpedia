-- Prove2me | solution 1 for lean_workbook_plus_16203
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:41:11.793694+00:00
-- url     : https://prove2.me/submissions/fa5bf384-8453-4cbb-84b0-36b168cfcbde

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℤ) (h : (a+b+c) ∣ (a^2+b^2+c^2)) : ∃ n : ℕ, (a+b+c) ∣ (a^n+b^n+c^n) :=
  ⟨2, h⟩
