-- Prove2me | solution 1 for lean_workbook_plus_24396
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:42:05.683115+00:00
-- url     : https://prove2.me/submissions/47244312-b7e1-41a5-93ca-bb96f5acd599

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ) : (4 * x ≡ 3 [ZMOD 5]) ↔ x ≡ 2 [ZMOD 5] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
