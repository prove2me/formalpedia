-- Prove2me | solution 1 for lean_workbook_plus_32903
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:46.266707+00:00
-- url     : https://prove2.me/submissions/6bed6249-95c6-40d1-84a4-7a5fee6a7551

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (n : ℕ) (a b c : ℤ) (h : b + c = 0) :
    a ^ (2 * n + 1) + b ^ (2 * n + 1) + c ^ (2 * n + 1) =
      (a + b + c) ^ (2 * n + 1) := by
  have hc : c = -b := by omega
  subst c
  have hodd : Odd (2 * n + 1) := ⟨n, by omega⟩
  rw [hodd.neg_pow]
  ring

#print axioms solution
