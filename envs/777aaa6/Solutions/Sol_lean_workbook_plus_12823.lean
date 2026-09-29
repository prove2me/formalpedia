-- Prove2me | solution 1 for lean_workbook_plus_12823
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:16.902817+00:00
-- url     : https://prove2.me/submissions/5eb58ee8-52a2-47a8-98fc-4f8a58d9942c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {x : ℤ} : x ^ 2 ≡ 0 [ZMOD 4] ∨ x ^ 2 ≡ 1 [ZMOD 4] := by
  have hm : x%4=0 ∨ x%4=1 ∨ x%4=2 ∨ x%4=3 := by omega
  change x^2%4=0%4 ∨ x^2%4=1%4
  rcases hm with hm|hm|hm|hm <;> norm_num [pow_two,Int.mul_emod,hm]
