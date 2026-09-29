-- Prove2me | solution 1 for mme_CW_canonical_four_literal_address_eq_support_pattern
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T19:46:11.941287+00:00
-- url     : https://prove2.me/submissions/aeff7e0f-15b6-46e3-93a4-31c9affa3e3d

import Definitions.Def_mme_CW_fourth_support_patterns
import Definitions.Def_mme_CW_fourth_literal_support_words
import Mathlib.Tactic

open BigOperators

namespace MME.StothersFourth

set_option autoImplicit false

private theorem cwSquareCoordGrade_zero (q : ℕ) :
    cwSquareCoordGrade q (cwZeroIndex q) = 0 := by
  simp [cwSquareCoordGrade, cwZeroIndex]

private theorem cwSquareCoordGrade_middle (q : ℕ) (i : Fin q) :
    cwSquareCoordGrade q (cwMiddleIndex q i) = 1 := by
  have hi := i.isLt
  simp [cwSquareCoordGrade, cwMiddleIndex]
  omega

private theorem cwSquareCoordGrade_top (q : ℕ) :
    cwSquareCoordGrade q (cwTopIndex q) = 2 := by
  simp [cwSquareCoordGrade, cwTopIndex]

private theorem canonicalSupportTerm_grade
    (q : ℕ) (i : Fin q) (r : Fin 6) (s : Fin 3) :
    (cwSquareCoordGrade q
      (cwLiteralTermTriple q (cwCanonicalSupportTerm q i r) s)).val =
      cwSingleSupportPattern r s := by
  fin_cases r <;> fin_cases s <;>
    simp [cwCanonicalSupportTerm, cwLiteralTermTriple,
      cwSingleSupportPattern, cwSquareCoordGrade_zero,
      cwSquareCoordGrade_middle, cwSquareCoordGrade_top]

end MME.StothersFourth

/-- The literal basis address of four canonical terms agrees with the
parameter-independent sum of their six support patterns. -/
theorem solution
    (q : ℕ) (i : Fin q) (r : Fin 4 → Fin 6) (s : Fin 3) :
    (MME.StothersFourth.cwCanonicalFourLiteralAddress q i r s).val =
      MME.StothersFourth.cwFourSupportNatAddress r s := by
  rw [show MME.StothersFourth.cwFourSupportNatAddress r s =
      MME.StothersFourth.cwSingleSupportPattern (r 0) s +
      MME.StothersFourth.cwSingleSupportPattern (r 1) s +
      MME.StothersFourth.cwSingleSupportPattern (r 2) s +
      MME.StothersFourth.cwSingleSupportPattern (r 3) s by
    simp [MME.StothersFourth.cwFourSupportNatAddress,
      Fin.sum_univ_succ, Nat.add_assoc]]
  simp only [MME.StothersFourth.cwCanonicalFourLiteralAddress,
    MME.StothersFourth.cwFourthPairGrade, MME.cwSquarePairGrade,
    MME.StothersFourth.cwFourthIndexOfLiteralTerms]
  rw [MME.StothersFourth.canonicalSupportTerm_grade,
    MME.StothersFourth.canonicalSupportTerm_grade,
    MME.StothersFourth.canonicalSupportTerm_grade,
    MME.StothersFourth.canonicalSupportTerm_grade]
  omega
