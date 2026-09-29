-- Prove2me | solution 1 for lean_workbook_plus_14798
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:02.299184+00:00
-- url     : https://prove2.me/submissions/01ea4e1a-32c5-40fe-8f71-1c6b9c087c7a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a : ℤ, a ≡ 2 [ZMOD 3] → a - 1 ≡ 1 [ZMOD 3] ∧ 2 * a + 1 ≡ 2 [ZMOD 3] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
