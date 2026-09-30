-- Prove2me | solution 1 for lean_workbook_plus_66236
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:38.353344+00:00
-- url     : https://prove2.me/submissions/e637ec61-0b4c-4f7f-a823-6bf9af5fc77c

import Mathlib
set_option autoImplicit false

theorem solution (a b c d : ℝ) : a+b+c+d=1 ∧ 8*a+4*b+2*c+d=17 ∧ 27*a+9*b+3*c+d=66 ∧ 64*a+16*b+4*c+d=166 ↔ a=3 ∧ b=-1.5 ∧ c=-0.5 ∧ d=0   := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    norm_num

#print axioms solution
