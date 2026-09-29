-- Prove2me | solution 1 for lean_workbook_plus_77838
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:43.539783+00:00
-- url     : https://prove2.me/submissions/91314512-5763-4c3c-bf66-b3fa7e306c29

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) : (4*n ≡ 4 [ZMOD 12] → n-1 ≡ 0 [ZMOD 3] → n ≡ 1 [ZMOD 3]) := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
