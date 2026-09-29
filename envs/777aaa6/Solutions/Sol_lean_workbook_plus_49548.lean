-- Prove2me | solution 1 for lean_workbook_plus_49548
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:27.411574+00:00
-- url     : https://prove2.me/submissions/ff3166bf-580f-4af6-9c29-56dc512b7a95

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ) : (11 * x ≡ 1 [ZMOD 3]) ↔ (x ≡ 2 [ZMOD 3]) := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
