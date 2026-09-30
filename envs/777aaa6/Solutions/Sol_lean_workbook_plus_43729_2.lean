-- Prove2me | solution 2 for lean_workbook_plus_43729
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:44.147636+00:00
-- url     : https://prove2.me/submissions/ebdf048a-91df-44ba-9462-2b27e562837b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℕ) (hp1 : p ≡ 3 [ZMOD 5]) (hp2 : p ≡ 3 [ZMOD 8]) : 40 ∣ 13 * p + 1 := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
