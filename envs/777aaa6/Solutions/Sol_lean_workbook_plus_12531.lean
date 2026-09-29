-- Prove2me | solution 1 for lean_workbook_plus_12531
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:26:46.540644+00:00
-- url     : https://prove2.me/submissions/7a8a36a3-159a-4d61-a398-180452fe1950

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (p a b : ℤ) (h : p - a^2 ∣ p - b^2) :
  p - a^2 ∣ (a + b) * (a - b) := by
  have hd := dvd_sub h (dvd_refl (p - a^2))
  convert hd using 1 <;> ring
