-- Prove2me | solution 1 for lean_workbook_plus_20614
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:57:48.290834+00:00
-- url     : https://prove2.me/submissions/206dd3a7-b410-4d0a-bb6a-df13ae9cbab1

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution {x : ℤ} (h : x%2 = 1) : x ^ 2 ≡ 1 [ZMOD 8] := by
  have hk : x%8=1 ∨ x%8=3 ∨ x%8=5 ∨ x%8=7 := by omega
  show x^2%8 = 1%8
  rcases hk with h|h|h|h <;> norm_num [pow_two,Int.mul_emod,h]
