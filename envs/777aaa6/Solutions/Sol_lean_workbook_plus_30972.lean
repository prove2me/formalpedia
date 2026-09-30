-- Prove2me | solution 1 for lean_workbook_plus_30972
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:32.190383+00:00
-- url     : https://prove2.me/submissions/7539d267-cce3-4ad7-b979-1b15708d3bec

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution
    (h : {(x, y) : ℤ × ℤ | y ^ 2 - x ^ 3 = 1} = {(2, 3), (2, -3)}) : False := by
  have hp : (0, 1) ∈ {(x, y) : ℤ × ℤ | y ^ 2 - x ^ 3 = 1} := by norm_num
  rw [h] at hp
  norm_num at hp

#print axioms solution
