-- Prove2me | solution 1 for lean_workbook_plus_23949
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:09:05.515007+00:00
-- url     : https://prove2.me/submissions/180cebef-7c35-4693-8ae6-3a53ab7b4578

import Mathlib.Analysis.Complex.Basic

theorem solution (a b m n : ℤ) (h₁ : a ≡ b [ZMOD m]) (h₂ : n ∣ m) : a ≡ b [ZMOD n] :=
  Int.ModEq.of_dvd h₂ h₁
