-- Prove2me | solution 1 for lean_workbook_plus_35679
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:07:11.838245+00:00
-- url     : https://prove2.me/submissions/d7705e9f-9319-46de-ba0b-fa824a10a4f6

import Mathlib.Analysis.Complex.Basic

theorem solution (a b m : ℕ) (p q : ℕ) (h1 : a ≡ b [ZMOD m]) (h2 : p ≡ q [ZMOD m]) : a * p ≡ b * q [ZMOD m] ∧ a + p ≡ b + q [ZMOD m] := by
  exact ⟨h1.mul h2, h1.add h2⟩
