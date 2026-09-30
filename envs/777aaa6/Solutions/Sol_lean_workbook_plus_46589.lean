-- Prove2me | solution 1 for lean_workbook_plus_46589
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:18:51.938024+00:00
-- url     : https://prove2.me/submissions/7bde54e4-9512-4a22-bb8e-48d53b080f68

import Mathlib.Analysis.Complex.Basic

theorem solution (A : ℕ) (hA : A ≡ -1 [ZMOD 8]) (hA' : A ≡ -1 [ZMOD 3]) : ∃ B : ℕ, B ≡ A [ZMOD 8] ∧ B ≡ A [ZMOD 3] :=
  ⟨A, Int.ModEq.refl _, Int.ModEq.refl _⟩
