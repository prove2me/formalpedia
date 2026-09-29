-- Prove2me | solution 1 for lean_workbook_plus_44544
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:41.537643+00:00
-- url     : https://prove2.me/submissions/4f1aaad2-676b-4224-967c-dd424e98d21c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) : n ≡ 1 [ZMOD 6] ∨ n ≡ 5 [ZMOD 6] ↔ n % 6 = 1 ∨ n % 6 = 5 := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
