-- Prove2me | solution 1 for lean_workbook_plus_33870
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:06:41.029831+00:00
-- url     : https://prove2.me/submissions/e2c274bf-5e39-49cc-a3fe-d1ef72710ea1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {m n : ℤ} (hm : m % 2 = 1) (hn : n % 2 = 1) : (m * n) % 2 = 1 := by
  rw [Int.mul_emod, hm, hn]
  norm_num
