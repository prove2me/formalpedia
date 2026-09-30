-- Prove2me | solution 2 for lean_workbook_plus_65777
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:06.199494+00:00
-- url     : https://prove2.me/submissions/bc32ca26-a52b-4601-83f4-f0c997752dcf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ) (hx: x ≡ 5 [ZMOD 7] ∧ x ≡ 7 [ZMOD 11] ∧ x ≡ 3 [ZMOD 13]) : x >= 197 := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
