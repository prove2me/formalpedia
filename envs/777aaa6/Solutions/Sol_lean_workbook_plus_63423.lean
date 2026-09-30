-- Prove2me | solution 1 for lean_workbook_plus_63423
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:40.299326+00:00
-- url     : https://prove2.me/submissions/429698b6-bbc8-4847-bcd2-c37730a7f4fb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution (p : ℤ) (hp : p % 2 = 1) :
    (p^2 - 1) % 2 = 0 ∧ (p^2 + 1) % 2 = 0 := by
  norm_num [pow_two, Int.sub_emod, Int.add_emod, Int.mul_emod, hp]
