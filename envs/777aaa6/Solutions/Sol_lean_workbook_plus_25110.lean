-- Prove2me | solution 1 for lean_workbook_plus_25110
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:15:02.282588+00:00
-- url     : https://prove2.me/submissions/14ce4d16-432b-4425-95d6-e2416df96d87

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution
    (h : ∀ x y z : ℤ,
      (x ^ 3 ≡ 0 [ZMOD 7] ∨ x ^ 3 ≡ 1 [ZMOD 7] ∨ x ^ 3 ≡ -1 [ZMOD 7]) →
      ¬ (x ^ 3 + y ^ 3 + z ^ 3 ≡ 1969 ^ 2 [ZMOD 7])) : False := by
  have hc := h (-1) (-1) (-1) (by norm_num [Int.ModEq])
  exact hc (by norm_num [Int.ModEq])

#print axioms solution
