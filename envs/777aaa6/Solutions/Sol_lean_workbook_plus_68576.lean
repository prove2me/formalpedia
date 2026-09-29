-- Prove2me | solution 1 for lean_workbook_plus_68576
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:35:00.51078+00:00
-- url     : https://prove2.me/submissions/3d7ddfec-0063-4f87-9a0e-97f41ac51381

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ) : (243 * x + 17 ≡ 101 [ZMOD 725]) ↔ x ≡ 63 [ZMOD 725] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
