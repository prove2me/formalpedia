-- Prove2me | solution 1 for lean_workbook_plus_25568
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:13:36.770395+00:00
-- url     : https://prove2.me/submissions/2d695cb1-93b6-4248-9fec-6f8ff36d925f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (n a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b ≠ 0)
    (h : n = a ^ 2 + 5 * b ^ 2) : ∃ a' b' : ℤ, a' ^ 2 + 5 * b' ^ 2 = n ^ 4 := by
  refine ⟨a ^ 4 - 30 * a ^ 2 * b ^ 2 + 25 * b ^ 4,
    4 * a * b * (a ^ 2 - 5 * b ^ 2), ?_⟩
  rw [h]
  ring

#print axioms solution
