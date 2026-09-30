-- Prove2me | solution 1 for lean_workbook_plus_67386
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:18:06.316743+00:00
-- url     : https://prove2.me/submissions/189cf615-836e-43b1-917e-190dc7f86992

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : ⌊x + 2⌋ = -2) : x ∈ Set.Icc (-4) (-3)   := by
  simp only [Set.mem_Icc, Int.floor_eq_iff, Int.cast_neg, Int.cast_ofNat, Int.cast_two,
    Int.cast_one, Int.cast_zero, neg_add, sub_eq_add_neg, neg_neg] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]

#print axioms solution
