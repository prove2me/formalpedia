-- Prove2me | solution 1 for BookSixth.tait_fox_five
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T23:51:08.322149+00:00
-- url     : https://prove2.me/submissions/565dad01-c2c0-4286-8f4b-518fa8d74f93

import Mathlib
import Definitions.Def_BookSixth

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators
open BookSixth

namespace BookFix

theorem tait_fox_five (a : Fin 6 → ZMod 5) :
    TaitFox a ↔ a 0 = a 2 ∧ a 2 = a 4 ∧ a 1 = a 3 ∧ a 3 = a 5 := by
  have hfive : (5 : ZMod 5) = 0 := by decide
  have hfour : (4 : ZMod 5) = -1 := by decide
  constructor
  · intro h
    have h0 : a 0 - a 3 = 4 * (a 1 - a 2) := h 0
    have h1 : a 1 - a 4 = 4 * (a 2 - a 3) := h 1
    have h2 : a 2 - a 5 = 4 * (a 3 - a 4) := h 2
    have h3 : a 3 - a 0 = 4 * (a 4 - a 5) := h 3
    have h4 : a 4 - a 1 = 4 * (a 5 - a 0) := h 4
    have h5 : a 5 - a 2 = 4 * (a 0 - a 1) := h 5
    rw [hfour] at h0 h1 h2 h3 h4 h5
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination 4*h0 - 4*h1 + 2*h2 - 2*h3 - (a 0 - a 2) * hfive
    · linear_combination 4*h2 - 4*h3 + 2*h4 - 2*h5 - (a 2 - a 4) * hfive
    · linear_combination 4*h1 - 4*h2 + 2*h3 - 2*h4 - (a 1 - a 3) * hfive
    · linear_combination 4*h3 - 4*h4 + 2*h5 - 2*h0 - (a 3 - a 5) * hfive
  · rintro ⟨e02, e24, e13, e35⟩ i
    have q2 : a 2 = a 0 := e02.symm
    have q3 : a 3 = a 1 := e13.symm
    have q4 : a 4 = a 0 := (e02.trans e24).symm
    have q5 : a 5 = a 1 := (e13.trans e35).symm
    fin_cases i
    · show a 0 - a 3 = 4 * (a 1 - a 2)
      simp only [q2, q3]; linear_combination (a 0 - a 1) * hfive
    · show a 1 - a 4 = 4 * (a 2 - a 3)
      simp only [q2, q3, q4]; linear_combination (a 1 - a 0) * hfive
    · show a 2 - a 5 = 4 * (a 3 - a 4)
      simp only [q2, q3, q4, q5]; linear_combination (a 0 - a 1) * hfive
    · show a 3 - a 0 = 4 * (a 4 - a 5)
      simp only [q3, q4, q5]; linear_combination (a 1 - a 0) * hfive
    · show a 4 - a 1 = 4 * (a 5 - a 0)
      simp only [q4, q5]; linear_combination (a 0 - a 1) * hfive
    · show a 5 - a 2 = 4 * (a 0 - a 1)
      simp only [q2, q5]; linear_combination (a 1 - a 0) * hfive


end BookFix

open scoped BigOperators in
open BookSixth in
theorem solution (a : Fin 6 → ZMod 5) :
    TaitFox a ↔ a 0 = a 2 ∧ a 2 = a 4 ∧ a 1 = a 3 ∧ a 3 = a 5 :=
  BookFix.tait_fox_five a
