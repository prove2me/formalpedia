-- Prove2me | solution 1 for lean_workbook_plus_61012
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:47:31.107949+00:00
-- url     : https://prove2.me/submissions/5b9bc346-5837-49dd-b003-3c9c49fbea61

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n:ℕ) : 4 ^ n ≡ 1 [ZMOD 3] := by
  have h : (4:ℤ) ≡ 1 [ZMOD 3] := by norm_num [Int.ModEq]
  simpa only [one_pow] using h.pow n
