-- Prove2me | solution 2 for lean_workbook_plus_81052
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:35.822675+00:00
-- url     : https://prove2.me/submissions/30e5ebb4-61fa-4135-8fd4-fa8c536a7a84

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℕ) (h1 : 9*x + 12*y ≡ 4 [ZMOD 47]) (h2 : 6*x + 7*y ≡ 14 [ZMOD 47]) : x ≡ 26 [ZMOD 47] ∧ y ≡ 20 [ZMOD 47] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
