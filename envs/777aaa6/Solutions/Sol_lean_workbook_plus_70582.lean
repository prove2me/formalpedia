-- Prove2me | solution 1 for lean_workbook_plus_70582
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:55.183439+00:00
-- url     : https://prove2.me/submissions/3734cf74-7edb-4b89-8294-b2ad89d5ecd0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℕ) (hp : p ≡ 3 [ZMOD 4]) : 2 ∣ (p + 1) / 2 ∧ 2 ∣ (p - 1) := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
