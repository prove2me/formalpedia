-- Prove2me | solution 1 for lean_workbook_plus_45750
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:01.769512+00:00
-- url     : https://prove2.me/submissions/2a0ec3ec-c9e5-48ad-94fd-edc47e8b2879

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z a b c : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hab : a = (x - y - z) / x) (hbc : b = (y - z - x) / y) (hca : c = (z - x - y) / z) : a * b * c + 4 = a * b + b * c + c * a := by
  rw [hab,hbc,hca]
  field_simp <;> ring
