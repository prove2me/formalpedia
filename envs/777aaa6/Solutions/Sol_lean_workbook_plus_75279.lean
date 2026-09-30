-- Prove2me | solution 1 for lean_workbook_plus_75279
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:53:05.578018+00:00
-- url     : https://prove2.me/submissions/2bef3d93-6690-42d9-941c-60990a532cd4

import Mathlib

theorem solution (p x y : ℤ) :
    p ∣ x^2 + x*y + y^2 → p ∣ (2*x + y)^2 + 3*y^2 := by
  rintro ⟨k, hk⟩
  refine ⟨4 * k, ?_⟩
  linear_combination 4 * hk
