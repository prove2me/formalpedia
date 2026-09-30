-- Prove2me | solution 1 for lean_workbook_plus_51342
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:44:26.240318+00:00
-- url     : https://prove2.me/submissions/cc3c17c4-b712-4c4f-a4ac-dbf1257a3519

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (p n : ℕ) (hp : p.Prime)
    (h : 2 ^ (2 ^ n) ≡ -1 [ZMOD p]) :
    2 ^ (2 ^ (n + 1)) ≡ 1 [ZMOD p] := by
  rw [pow_succ, pow_mul]
  simpa using h.pow 2

#print axioms solution
