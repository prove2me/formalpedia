-- Prove2me | solution 1 for lean_workbook_plus_29879
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:23.566768+00:00
-- url     : https://prove2.me/submissions/75905da8-1ad3-44e2-95d0-53b271675445

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c x y z p q r : ℝ} (ha : a + b + c = 9) (hb : a * b + b * c + c * a = 24) (hx : x = a - 1) (hy : y = b - 1) (hz : z = c - 1) (hp : p = a - 2) (hq : q = b - 2) (hr : r = c - 2) : x + y + z = 6 ∧ x * y + y * z + z * x = 9 ∧ p + q + r = 3 ∧ p * q + q * r + r * p = 0 := by
  rw [hx,hy,hz,hp,hq,hr]
  constructor
  · linarith
  constructor
  · nlinarith
  constructor
  · linarith
  · nlinarith
