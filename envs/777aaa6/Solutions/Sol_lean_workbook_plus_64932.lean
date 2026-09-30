-- Prove2me | solution 1 for lean_workbook_plus_64932
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:15:45.169463+00:00
-- url     : https://prove2.me/submissions/b7fe6797-79b8-449a-b283-68c29ad6c31e

import Mathlib
set_option autoImplicit false

theorem solution (x n : ℕ) (hx : x^3 ≡ 1 [ZMOD n]) : (x - 1) * (x^2 + x + 1) ≡ 0 [ZMOD n]   := by
  have h := hx.sub (show (1 : ℤ) ≡ 1 [ZMOD n] from rfl)
  convert h using 1 <;> ring

#print axioms solution
