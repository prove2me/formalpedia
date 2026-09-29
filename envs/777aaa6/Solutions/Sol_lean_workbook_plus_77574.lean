-- Prove2me | solution 1 for lean_workbook_plus_77574
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:41.185764+00:00
-- url     : https://prove2.me/submissions/83c06957-0683-4e00-966a-b290f60308ec

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (h₁ : n ≡ 0 [ZMOD 2]) (h₂ : 5 ∣ n) : 10 ∣ n := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
