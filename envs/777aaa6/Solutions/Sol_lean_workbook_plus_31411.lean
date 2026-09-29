-- Prove2me | solution 1 for lean_workbook_plus_31411
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:58.447024+00:00
-- url     : https://prove2.me/submissions/5c6a8a78-ebd4-4746-87b9-cfc82a087725

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ) (hx: x > 4) (h1 : x-1 ≡ 0 [ZMOD 4]) (h2 : x ≡ 0 [ZMOD 3]) : x >= 9 := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
