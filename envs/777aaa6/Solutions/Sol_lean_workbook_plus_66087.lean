-- Prove2me | solution 1 for lean_workbook_plus_66087
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:45.068679+00:00
-- url     : https://prove2.me/submissions/2a27339a-2b40-4e35-8c40-6101f9f9eb26

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℤ) (ha : ¬ a ≡ 0 [ZMOD 3]) : a ^ 2 ≡ 1 [ZMOD 3] := by
  have hm : a%3=0 ∨ a%3=1 ∨ a%3=2 := by omega
  rcases hm with hm|hm|hm
  · exact (ha (by simpa [Int.ModEq] using hm)).elim
  · norm_num [Int.ModEq,pow_two,Int.mul_emod,hm]
  · norm_num [Int.ModEq,pow_two,Int.mul_emod,hm]
