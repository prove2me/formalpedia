-- Prove2me | solution 1 for lean_workbook_plus_63048
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:47:37.088713+00:00
-- url     : https://prove2.me/submissions/64c325e8-a80e-4745-85bd-fd8a00195ec9

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {p : ℝ} (hp : p > -1) {n : ℕ} (hn : n ≥ 1) : (1 + p)^n ≥ 1 + n * p := by
  exact one_add_mul_le_pow (by linarith : -2 ≤ p) n
