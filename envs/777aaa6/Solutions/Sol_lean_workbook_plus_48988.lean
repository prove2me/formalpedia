-- Prove2me | solution 1 for lean_workbook_plus_48988
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:07.430184+00:00
-- url     : https://prove2.me/submissions/61b68118-ed22-4a4d-bd7c-a02d39000bd7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℤ) : a^2 ≡ 0 [ZMOD 4] ∨ a^2 ≡ 1 [ZMOD 4] := by
  have hm : a%4=0 ∨ a%4=1 ∨ a%4=2 ∨ a%4=3 := by omega
  change a^2%4=0%4 ∨ a^2%4=1%4
  rcases hm with hm|hm|hm|hm <;> norm_num [pow_two,Int.mul_emod,hm]
