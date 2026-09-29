-- Prove2me | solution 1 for lean_workbook_plus_67806
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:40:58.510372+00:00
-- url     : https://prove2.me/submissions/19531c57-6bc8-4533-9dfd-bbe1605bf712

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c d : ℕ, a * 10 ^ 3 + b * 10 ^ 2 + c * 10 + d ≡ 0 [ZMOD 8] ↔ b * 10 ^ 2 + c * 10 + d ≡ 0 [ZMOD 8] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
