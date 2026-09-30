-- Prove2me | solution 1 for lean_workbook_plus_2623
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:52.381442+00:00
-- url     : https://prove2.me/submissions/2a0ba7b2-6a5e-4b29-902f-699c4439b0ad

import Mathlib

theorem solution (x y z : ℤ) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    5 * (x - y) * (y - z) * (z - x) ∣ (x - y) ^ 5 + (y - z) ^ 5 + (z - x) ^ 5 := by
  refine ⟨x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x, ?_⟩
  ring
