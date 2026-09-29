-- Prove2me | solution 1 for lean_workbook_plus_39666
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:45.731654+00:00
-- url     : https://prove2.me/submissions/c285ec41-18e6-4b62-96cc-c9f744ccbc7e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ n : ℤ, n ^ 7 - n ≡ 0 [ZMOD 2] := by
  intro n
  have hm : n%2=0 ∨ n%2=1 := by omega
  rcases hm with h|h <;> norm_num [Int.ModEq,Int.sub_emod,pow_succ,Int.mul_emod,h]
