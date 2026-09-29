-- Prove2me | solution 1 for lean_workbook_plus_3305
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:01:27.626983+00:00
-- url     : https://prove2.me/submissions/b8684ce2-3b32-419e-8bca-39dd8c339da7

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ k : ℕ, 2 ^ (3 * k) ≡ 1 [ZMOD 7] := by
  intro k
  have h : Int.ModEq 7 (2^3) 1 := by norm_num [Int.ModEq]
  simpa [pow_mul] using h.pow k
