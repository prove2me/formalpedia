-- Prove2me | solution 1 for lean_workbook_plus_13877
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:50.050072+00:00
-- url     : https://prove2.me/submissions/b1911ce5-f2e9-4ee6-a701-35e349e4fbf3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ d e : ℤ, (d * e ≡ -1 [ZMOD 24]) → (d^2 * e ≡ e [ZMOD 24]) ∧ (d^2 * e ≡ -d [ZMOD 24]) → d + e ≡ 0 [ZMOD 24] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
