-- Prove2me | solution 1 for lean_workbook_plus_44546
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:01:09.653298+00:00
-- url     : https://prove2.me/submissions/8be132d0-e474-47e9-9b3c-ca6bdd544176

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.GroupWithZero.Divisibility

theorem solution (a b c d : ℤ) (ha : a ≠ 0) (hd : d ≠ 0) :
    (a * b ≡ a * c [ZMOD a * d]) ↔ (b ≡ c [ZMOD d]) := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, ← mul_sub,
    mul_dvd_mul_iff_left ha]

#print axioms solution
