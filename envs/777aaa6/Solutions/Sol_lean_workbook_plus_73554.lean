-- Prove2me | solution 1 for lean_workbook_plus_73554
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:48.203192+00:00
-- url     : https://prove2.me/submissions/9517848b-b266-4803-9eb5-add2b5ac234b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ) : (11 * x ≡ 1 [ZMOD 3]) ↔ x ≡ 2 [ZMOD 3] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
