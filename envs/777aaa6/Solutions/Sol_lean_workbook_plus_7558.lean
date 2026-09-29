-- Prove2me | solution 1 for lean_workbook_plus_7558
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:58.648564+00:00
-- url     : https://prove2.me/submissions/c69ec02a-703e-4027-b549-ffc8d14833a5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℤ) : 2 * n ≡ 0 [ZMOD 3] → n ≡ 0 [ZMOD 3] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
