-- Prove2me | solution 1 for lean_workbook_plus_49750
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:06:27.347713+00:00
-- url     : https://prove2.me/submissions/6d6b17f8-709c-443b-971c-ea8fe7e2468e

import Mathlib.Analysis.Complex.Basic
theorem solution : 3 ^ 2005 + 7 ^ 1426 ≡ 4 [ZMOD 16] := by
  have h3 : (3:ℤ) ^ 4 ≡ 1 [ZMOD 16] := by decide
  have h7 : (7:ℤ) ^ 2 ≡ 1 [ZMOD 16] := by decide
  have e3 : (3:ℤ) ^ 2005 = ((3:ℤ) ^ 4) ^ 501 * 3 := by rw [← pow_mul, ← pow_succ]
  have e7 : (7:ℤ) ^ 1426 = ((7:ℤ) ^ 2) ^ 713 := by rw [← pow_mul]
  calc (3:ℤ) ^ 2005 + 7 ^ 1426 = ((3:ℤ) ^ 4) ^ 501 * 3 + ((7:ℤ) ^ 2) ^ 713 := by rw [e3, e7]
    _ ≡ 1 ^ 501 * 3 + 1 ^ 713 [ZMOD 16] := ((h3.pow 501).mul_right 3).add (h7.pow 713)
    _ = 4 := by norm_num
