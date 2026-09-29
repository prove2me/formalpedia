-- Prove2me | solution 1 for lean_workbook_plus_69442
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:01.220058+00:00
-- url     : https://prove2.me/submissions/0a1edc47-3fd9-4885-919b-cca0c8d011e1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (h1 : 7 ∣ n + 1) (h2 : 191 ∣ n + 1) : n ≡ 1336 [ZMOD 1337] := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)
