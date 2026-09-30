-- Prove2me | solution 1 for lean_workbook_plus_68473
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:16:24.981834+00:00
-- url     : https://prove2.me/submissions/8f1e7c72-f8b2-4cf9-9ef1-3f6627f2bbcd

import Mathlib
set_option autoImplicit false

theorem solution : 2222 ^ 5555 + 5555 ^ 2222 ≡ 0 [ZMOD 7]   := by
  have hbase3 : (2222 : ℤ) ≡ 3 [ZMOD 7] := by norm_num [Int.ModEq]
  have hbase4 : (5555 : ℤ) ≡ 4 [ZMOD 7] := by norm_num [Int.ModEq]
  have hperiod3 : (3 : ℤ) ^ 6 ≡ 1 [ZMOD 7] := by norm_num [Int.ModEq]
  have hperiod4 : (4 : ℤ) ^ 3 ≡ 1 [ZMOD 7] := by norm_num [Int.ModEq]
  have hreduce3 : (3 : ℤ) ^ 5555 ≡ 3 ^ 5 [ZMOD 7] := by
    change (3 : ℤ) ^ (6 * 925 + 5) ≡ 3 ^ 5 [ZMOD 7]
    simpa only [pow_add, pow_mul, one_pow, one_mul] using
      (hperiod3.pow 925).mul (Int.ModEq.refl ((3 : ℤ) ^ 5))
  have hreduce4 : (4 : ℤ) ^ 2222 ≡ 4 ^ 2 [ZMOD 7] := by
    change (4 : ℤ) ^ (3 * 740 + 2) ≡ 4 ^ 2 [ZMOD 7]
    simpa only [pow_add, pow_mul, one_pow, one_mul] using
      (hperiod4.pow 740).mul (Int.ModEq.refl ((4 : ℤ) ^ 2))
  have hsmall3 : (3 : ℤ) ^ 5 ≡ 5 [ZMOD 7] := by norm_num [Int.ModEq]
  have hsmall4 : (4 : ℤ) ^ 2 ≡ 2 [ZMOD 7] := by norm_num [Int.ModEq]
  have hfirst := (hbase3.pow 5555).trans (hreduce3.trans hsmall3)
  have hsecond := (hbase4.pow 2222).trans (hreduce4.trans hsmall4)
  exact (hfirst.add hsecond).trans (by norm_num [Int.ModEq])

#print axioms solution
