-- Prove2me | solution 1 for lean_workbook_plus_72482
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:11.956549+00:00
-- url     : https://prove2.me/submissions/6d1f2a12-e4b8-42d0-a294-b85ca637264c

import Mathlib

set_option autoImplicit false

theorem solution (x y z : ℤ) (h₀ : x ^ 2 ≡ 0 [ZMOD 3])
    (h₁ : y ^ 2 ≡ 0 [ZMOD 3]) (h₂ : z ^ 2 ≡ 0 [ZMOD 3])
    (h₃ : x ^ 2 + y ^ 2 + z ^ 2 = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  have hx : x = 0 := by nlinarith [sq_nonneg y, sq_nonneg z]
  have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg z]
  have hz : z = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  exact ⟨hx, hy, hz⟩
