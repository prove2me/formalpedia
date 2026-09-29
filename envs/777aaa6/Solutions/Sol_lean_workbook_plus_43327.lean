-- Prove2me | solution 1 for lean_workbook_plus_43327
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:04:56.141858+00:00
-- url     : https://prove2.me/submissions/7c462d70-15aa-45b3-bb3e-6b9f0bdf8ded

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) : 7 ^ (4 * n + 1) ≡ 7 [ZMOD 10] := by
  have h : (7 : ℤ) ^ 4 ≡ 1 [ZMOD 10] := by decide
  have hp := (h.pow n).mul_right 7
  simpa [pow_mul, pow_succ] using hp
