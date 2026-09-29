-- Prove2me | solution 1 for lean_workbook_plus_9328
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:19.286282+00:00
-- url     : https://prove2.me/submissions/d08eecf8-2705-4aba-8c08-43bd2193cf21

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℤ) : (k ^ 2 ≡ 0 [ZMOD 3]) ∨ (k ^ 2 ≡ 1 [ZMOD 3]) ∨ (k ^ 2 ≡ -1 [ZMOD 3]) := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
