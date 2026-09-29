-- Prove2me | solution 1 for lean_workbook_plus_37275
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:37:39.253561+00:00
-- url     : https://prove2.me/submissions/e3092fbb-1d78-4523-b0b3-e224b7d87efe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b m : ℤ)
  (h₀ : 0 < m)
  (h₁ : a ≡ b [ZMOD m]) :
  a % m = b % m := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
