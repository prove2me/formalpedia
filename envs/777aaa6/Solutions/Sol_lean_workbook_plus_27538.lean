-- Prove2me | solution 1 for lean_workbook_plus_27538
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:42:03.22536+00:00
-- url     : https://prove2.me/submissions/2901cd01-e4d6-46c6-b258-2507078bfb85

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ) : 108 * x ≡ 171 [ZMOD 529] ↔ x ≡ 222 [ZMOD 529] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
