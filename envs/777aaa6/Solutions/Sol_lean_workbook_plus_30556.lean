-- Prove2me | solution 1 for lean_workbook_plus_30556
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:41:01.600516+00:00
-- url     : https://prove2.me/submissions/9e3b4fb7-29b1-45bd-ba7c-bf783dc6152a

import Mathlib.Analysis.Complex.Basic

theorem solution (p : ℕ) (k : ℕ) (h₁ : k < 4 * p + 1) (h₂ : k ^ 4 ≡ 1 [ZMOD 4 * p + 1]) : ∃ m : ℕ, k ^ m ≡ 1 [ZMOD 4 * p + 1] ∧ m < 4 * p + 1 :=
  ⟨0, by simp, by omega⟩
