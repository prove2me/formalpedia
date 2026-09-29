-- Prove2me | solution 1 for lean_workbook_plus_4234
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:09:42.353674+00:00
-- url     : https://prove2.me/submissions/21e5918f-c7ac-40b5-9dc8-0a4a03874af7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℤ) : (a + b) ^ 2 - a * b ≡ 0 [ZMOD 5] ↔ (2 * a + b) ^ 2 + 3 * b ^ 2 ≡ 0 [ZMOD 5] := by
  have hid : (2*a+b)^2+3*b^2 = 4*((a+b)^2-a*b) := by ring
  have helper (t : ℤ) : t ≡ 0 [ZMOD 5] ↔ 4*t ≡ 0 [ZMOD 5] := by
    simp only [Int.ModEq]
    omega
  rw [hid]
  exact helper _
