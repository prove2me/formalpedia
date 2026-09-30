-- Prove2me | solution 1 for lean_workbook_plus_9656
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:56:18.188715+00:00
-- url     : https://prove2.me/submissions/9b8c988a-d473-46dd-9b03-c635be78b8ec

import Mathlib.Analysis.Complex.Basic

theorem solution {x y : ℤ} (h : x^2 - 2 ≡ -y [ZMOD 4]) : y ≡ 1 [ZMOD 4] ∨ y ≡ 2 [ZMOD 4] := by
  unfold Int.ModEq at *
  have h4 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  have hsq : x^2 % 4 = 0 ∨ x^2 % 4 = 1 := by
    rcases h4 with h4|h4|h4|h4 <;> simp [pow_two, Int.mul_emod, h4]
  omega
