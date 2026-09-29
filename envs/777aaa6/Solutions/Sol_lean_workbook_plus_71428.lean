-- Prove2me | solution 1 for lean_workbook_plus_71428
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:57.948589+00:00
-- url     : https://prove2.me/submissions/4aeaada3-e142-42b8-b8dd-6a1bdc8e586a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (h₁ : n ≡ 4 [ZMOD 9]) (h₂ : n ≡ 1 [ZMOD 5]) (h₃ : n ≡ 5 [ZMOD 8]) : n ≡ 1 [ZMOD 3] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
