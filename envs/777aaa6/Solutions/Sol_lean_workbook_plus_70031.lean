-- Prove2me | solution 1 for lean_workbook_plus_70031
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:17.750017+00:00
-- url     : https://prove2.me/submissions/fb396820-7896-4908-84ae-a2ccdeaec1a7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : 5555 ^ 5555 ≡ 5 [ZMOD 9] := by
  have h : (5555:ℤ) ≡ 2 [ZMOD 9] := by norm_num [Int.ModEq]
  have hp := h.pow 5555
  have h6 : (2:ℤ)^6 ≡ 1 [ZMOD 9] := by norm_num [Int.ModEq]
  have ht : (2:ℤ)^5555 ≡ 5 [ZMOD 9] := by
    calc
      (2:ℤ)^5555=(2^6)^925*2^5 := by rw [← pow_mul,← pow_add]
      _ ≡ 1^925*2^5 [ZMOD 9] := (h6.pow 925).mul Int.ModEq.rfl
      _ ≡ 5 [ZMOD 9] := by norm_num [Int.ModEq]
  exact hp.trans ht
