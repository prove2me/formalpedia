-- Prove2me | solution 1 for lean_workbook_plus_74512
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:48:46.034067+00:00
-- url     : https://prove2.me/submissions/a31c0bd8-8260-43a2-ae88-aa107b53b4ae

import Mathlib
set_option autoImplicit false

theorem solution : 3 ^ 2001 * 7 ^ 2002 * 13 ^ 2003 ≡ 9 [ZMOD 10]   := by
  have h3 : (3 : ℤ) ^ 4 ≡ 1 [ZMOD 10] := by norm_num [Int.ModEq]
  have h7 : (7 : ℤ) ^ 4 ≡ 1 [ZMOD 10] := by norm_num [Int.ModEq]
  have h13 : (13 : ℤ) ^ 4 ≡ 1 [ZMOD 10] := by norm_num [Int.ModEq]
  have p3 : (3 : ℤ) ^ 2001 ≡ 3 [ZMOD 10] := by
    have h := (Int.ModEq.pow 500 h3).mul
      (show (3 : ℤ) ^ 1 ≡ 3 [ZMOD 10] by norm_num [Int.ModEq])
    simpa only [← pow_mul, ← pow_add, one_pow, one_mul] using h
  have p7 : (7 : ℤ) ^ 2002 ≡ 9 [ZMOD 10] := by
    have h := (Int.ModEq.pow 500 h7).mul
      (show (7 : ℤ) ^ 2 ≡ 9 [ZMOD 10] by norm_num [Int.ModEq])
    simpa only [← pow_mul, ← pow_add, one_pow, one_mul] using h
  have p13 : (13 : ℤ) ^ 2003 ≡ 7 [ZMOD 10] := by
    have h := (Int.ModEq.pow 500 h13).mul
      (show (13 : ℤ) ^ 3 ≡ 7 [ZMOD 10] by norm_num [Int.ModEq])
    simpa only [← pow_mul, ← pow_add, one_pow, one_mul] using h
  exact ((p3.mul p7).mul p13).trans (by norm_num [Int.ModEq])

#print axioms solution
