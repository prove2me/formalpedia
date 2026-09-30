-- Prove2me | solution 1 for lean_workbook_plus_43729
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:51:54.982998+00:00
-- url     : https://prove2.me/submissions/5b57910e-d35d-4a0a-be80-af0f86df4c2c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (p : ℕ) (hp1 : p ≡ 3 [ZMOD 5])
    (hp2 : p ≡ 3 [ZMOD 8]) : 40 ∣ 13 * p + 1 := by
  simp only [Int.ModEq] at hp1 hp2
  omega

#print axioms solution
