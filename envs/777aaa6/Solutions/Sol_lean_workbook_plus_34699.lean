-- Prove2me | solution 1 for lean_workbook_plus_34699
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:39:25.925728+00:00
-- url     : https://prove2.me/submissions/940c0f7f-829c-4142-9ef0-4f5c3e3ab0d1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℤ, x ^ 3 ≡ 0 [ZMOD 3] ∨ x ^ 3 ≡ 1 [ZMOD 3] ∨ x ^ 3 ≡ 2 [ZMOD 3] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
