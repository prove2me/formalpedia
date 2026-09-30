-- Prove2me | solution 1 for lean_workbook_plus_70553
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:37:52.793828+00:00
-- url     : https://prove2.me/submissions/6c8d83ce-852a-45b7-80ee-be6e866b66e5

import Mathlib

set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 10000

theorem certificate_1024 : (2 : Int) ^ 1024 ≡ 917050 [ZMOD 1093 ^ 2] := by
  norm_num [Int.ModEq]

theorem certificate_64 : (2 : Int) ^ 64 ≡ 606814 [ZMOD 1093 ^ 2] := by
  norm_num [Int.ModEq]

theorem solution : 2 ^ 1092 ≡ 1 [ZMOD 1093 ^ 2] := by
  have h4 : (2 : Int) ^ 4 ≡ 16 [ZMOD 1093 ^ 2] := by norm_num [Int.ModEq]
  have h := (certificate_1024.mul certificate_64).mul h4
  have hprod : (917050 : Int) * 606814 * 16 ≡ 1 [ZMOD 1093 ^ 2] := by
    norm_num [Int.ModEq]
  have hexp : (2 : Int) ^ 1092 = 2 ^ 1024 * 2 ^ 64 * 2 ^ 4 := by
    rw [← pow_add, ← pow_add]
  rw [hexp]
  exact h.trans hprod

#print axioms solution
