-- Prove2me | solution 1 for lean_workbook_plus_37693
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:44:34.337356+00:00
-- url     : https://prove2.me/submissions/caf086d8-3067-4b1b-a32c-40a805958579

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution :
  1971^1970 ≡ 12 [ZMOD 13] := by
  have h4 : (1971 : ℤ)^4 ≡ 1 [ZMOD 13] := by norm_num [Int.ModEq]
  have h2 : (1971 : ℤ)^2 ≡ 12 [ZMOD 13] := by norm_num [Int.ModEq]
  rw [show 1970 = 4*492+2 by decide,pow_add,pow_mul]
  simpa only [one_pow,one_mul] using (h4.pow 492).mul h2
