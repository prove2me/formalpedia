-- Prove2me | solution 1 for lean_workbook_plus_36773
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:05:55.031209+00:00
-- url     : https://prove2.me/submissions/2c23b36e-5649-4dec-bb9b-023aacaa753e

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) : 2 ^ (10 * n) ≡ 1 [ZMOD 11] := by
  have h : (2 : ℤ) ^ 10 ≡ 1 [ZMOD 11] := by decide
  simpa [pow_mul] using h.pow n
