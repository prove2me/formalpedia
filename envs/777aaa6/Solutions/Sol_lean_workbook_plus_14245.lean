-- Prove2me | solution 1 for lean_workbook_plus_14245
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:14:26.482968+00:00
-- url     : https://prove2.me/submissions/617110af-039a-4e5b-b596-1c879032bf5b

import Mathlib.Analysis.Complex.Basic

theorem solution : 8 ^ 2003 ≡ 8 [ZMOD 49] := by
  have h7 : (8:ℤ) ^ 7 ≡ 1 [ZMOD 49] := by decide
  have h : (8:ℤ) ^ 2003 = ((8:ℤ) ^ 7) ^ 286 * 8 := by
    rw [← pow_mul, ← pow_succ]
  rw [h]
  calc ((8:ℤ) ^ 7) ^ 286 * 8 ≡ 1 ^ 286 * 8 [ZMOD 49] := (h7.pow 286).mul_right 8
    _ = 8 := by norm_num
