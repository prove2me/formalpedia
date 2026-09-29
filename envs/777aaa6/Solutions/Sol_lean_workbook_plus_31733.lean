-- Prove2me | solution 1 for lean_workbook_plus_31733
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:03.51191+00:00
-- url     : https://prove2.me/submissions/3fabf907-7cbc-45f2-9ab6-2ffc9f10bafa

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℤ) : x ^ 3 ≡ x [ZMOD 3] := by
  have hm : x%3=0 ∨ x%3=1 ∨ x%3=2 := by omega
  rcases hm with h|h|h <;> norm_num [Int.ModEq,pow_succ,Int.mul_emod,h]
