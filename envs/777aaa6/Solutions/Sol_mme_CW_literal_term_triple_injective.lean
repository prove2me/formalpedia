-- Prove2me | solution 1 for mme_CW_literal_term_triple_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:03:41.031613+00:00
-- url     : https://prove2.me/submissions/ba88e8f8-66a2-47bf-bde2-61b172c0a170

import Definitions.Def_mme_CW_fourth_literal_support_words
import Mathlib.Tactic

open MME.StothersFourth

set_option autoImplicit false

/-- The three basis coordinates uniquely determine a literal CW summand. -/
theorem solution (q : ℕ) :
    Function.Injective (cwLiteralTermTriple q) := by
  intro x y h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  rcases x with x | x
  · obtain ⟨i, r⟩ := x
    rcases y with y | y
    · obtain ⟨j, t⟩ := y
      fin_cases r <;> fin_cases t <;>
        simp [cwLiteralTermTriple, cwZeroIndex, cwMiddleIndex] at h0 h1 h2 ⊢ <;>
        omega
    · fin_cases r <;> fin_cases y <;>
        simp [cwLiteralTermTriple, cwZeroIndex, cwMiddleIndex,
          cwTopIndex] at h0 h1 h2
  · rcases y with y | y
    · obtain ⟨j, t⟩ := y
      fin_cases x <;> fin_cases t <;>
        simp [cwLiteralTermTriple, cwZeroIndex, cwMiddleIndex,
          cwTopIndex] at h0 h1 h2
    · fin_cases x <;> fin_cases y <;>
        simp [cwLiteralTermTriple, cwZeroIndex, cwTopIndex] at h0 h1 h2 ⊢

