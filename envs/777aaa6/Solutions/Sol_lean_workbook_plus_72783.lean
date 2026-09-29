-- Prove2me | solution 1 for lean_workbook_plus_72783
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:52.821809+00:00
-- url     : https://prove2.me/submissions/ce899963-4730-4f1c-8b85-4f4929af692f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℕ) (h₁ : 1 ≤ a ∧ a ≤ 9) (h₂ : 0 ≤ b ∧ b ≤ 9) (h₃ : 0 ≤ c ∧ c ≤ 9) : a * 100 + b * 10 + c ≡ 0 [ZMOD 6] ↔ a * 100 + b * 10 + c ≡ 0 [ZMOD 3] ∧ a * 100 + b * 10 + c ≡ 0 [ZMOD 2] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
