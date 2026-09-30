-- Prove2me | solution 1 for lean_workbook_plus_27616
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:56:02.390295+00:00
-- url     : https://prove2.me/submissions/81234bf5-8db6-4a05-bebf-43520dad6f54

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem power_equivalence (y : Real) : y ^ 2 = 2 ↔ y ^ 6 = 8 := by
  constructor
  · intro h
    calc
      y ^ 6 = (y ^ 2) ^ 3 := by ring
      _ = 8 := by rw [h]; norm_num
  · intro h
    have hf : (y ^ 2 - 2) * ((y ^ 2) ^ 2 + 2 * y ^ 2 + 4) = 0 := by
      calc
        (y ^ 2 - 2) * ((y ^ 2) ^ 2 + 2 * y ^ 2 + 4) = y ^ 6 - 8 := by ring
        _ = 0 := by rw [h]; norm_num
    have hp : 0 < (y ^ 2) ^ 2 + 2 * y ^ 2 + 4 := by positivity
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right (ne_of_gt hp))

theorem solution (y : Real) : y ^ 2 = 2 ∨ y ^ 6 = 8 ↔ y ^ 2 = 2 ∧ y ^ 6 = 8 := by
  constructor
  · rintro (h | h)
    · exact ⟨h, (power_equivalence y).mp h⟩
    · exact ⟨(power_equivalence y).mpr h, h⟩
  · intro h
    exact Or.inl h.1

#print axioms solution
