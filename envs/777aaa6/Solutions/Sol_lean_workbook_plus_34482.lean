-- Prove2me | solution 1 for lean_workbook_plus_34482
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:56.109708+00:00
-- url     : https://prove2.me/submissions/4f6eddd1-d8b9-4f65-92ca-8c063697e53e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (hn: n > 0) : (n ≡ 2 [ZMOD 4]) ∨ (n ≡ 3 [ZMOD 4]) ↔ (n % 4 = 2 ∨ n % 4 = 3) := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
