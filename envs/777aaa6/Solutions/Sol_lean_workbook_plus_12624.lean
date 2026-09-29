-- Prove2me | solution 1 for lean_workbook_plus_12624
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:44:33.078432+00:00
-- url     : https://prove2.me/submissions/b8b817dc-5324-46b8-9410-838bd32302a4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : 793 ^ 4000 ≡ 1 [ZMOD 10000] := by
  have p1 : (793 : ℤ)^1 ≡ 793 [ZMOD 10000] := by norm_num [Int.ModEq]
  have p3 : (793 : ℤ)^3 ≡ 7257 [ZMOD 10000] := by
    rw [show 3 = 1*2+1 by decide,pow_add,pow_mul]
    exact ((p1.pow 2).mul p1).trans (by norm_num [Int.ModEq])
  have p6 : (793 : ℤ)^6 ≡ 4049 [ZMOD 10000] := by
    rw [show 6 = 3*2 by decide,pow_mul]
    exact (p3.pow 2).trans (by norm_num [Int.ModEq])
  have p12 : (793 : ℤ)^12 ≡ 4401 [ZMOD 10000] := by
    rw [show 12 = 6*2 by decide,pow_mul]
    exact (p6.pow 2).trans (by norm_num [Int.ModEq])
  have p25 : (793 : ℤ)^25 ≡ 9193 [ZMOD 10000] := by
    rw [show 25 = 12*2+1 by decide,pow_add,pow_mul]
    exact ((p12.pow 2).mul p1).trans (by norm_num [Int.ModEq])
  have p50 : (793 : ℤ)^50 ≡ 1249 [ZMOD 10000] := by
    rw [show 50 = 25*2 by decide,pow_mul]
    exact (p25.pow 2).trans (by norm_num [Int.ModEq])
  have p100 : (793 : ℤ)^100 ≡ 1 [ZMOD 10000] := by
    rw [show 100 = 50*2 by decide,pow_mul]
    exact (p50.pow 2).trans (by norm_num [Int.ModEq])
  simpa only [← pow_mul,one_pow] using p100.pow 40
