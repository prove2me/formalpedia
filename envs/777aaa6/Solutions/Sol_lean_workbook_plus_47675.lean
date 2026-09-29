-- Prove2me | solution 1 for lean_workbook_plus_47675
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:32.071045+00:00
-- url     : https://prove2.me/submissions/99e23692-d82d-41bf-98f1-05f20f9ca2c1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ) : a = 7 ^ 10 → a ≡ 1 [ZMOD 11] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
