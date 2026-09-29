-- Prove2me | solution 1 for lean_workbook_plus_33467
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:51.56854+00:00
-- url     : https://prove2.me/submissions/ceecc87b-886c-445f-823f-2623a801e489

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ n : ℕ, (n^2 + n + 2) / 2 ≥ 2007 → n ≥ 63 := by
  intro n h
  by_contra hn
  have hn : n ≤ 62 := by omega
  have hs := Nat.mul_le_mul hn hn
  norm_num [pow_two] at hs h
  omega
