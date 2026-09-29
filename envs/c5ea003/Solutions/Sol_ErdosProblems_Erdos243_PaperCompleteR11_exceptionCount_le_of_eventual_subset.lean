-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.exceptionCount_le_of_eventual_subset
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:20:31.535692+00:00
-- url     : https://prove2.me/submissions/055e9c49-30f7-45b2-8622-b76c3ee27368

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Finite-prefix and constant transport for the literal
lower asymptotic density used throughout the R11 window arguments. -/

namespace ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR9
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution (E F : Set ℕ) (T X : ℕ)
    (hsub : ∀ n, T ≤ n → n ∈ E → n ∈ F) :
    exceptionCount E X ≤ T + exceptionCount F X := by
  classical
  have hs : exceptionFinset E X ⊆ Finset.range T ∪ exceptionFinset F X := by
    intro n hn
    obtain ⟨hnX, hnE⟩ := Finset.mem_filter.mp hn
    by_cases hnT : n < T
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr hnT))
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hnX, hsub n (by omega) hnE⟩))
  calc
    exceptionCount E X ≤ (Finset.range T ∪ exceptionFinset F X).card :=
      Finset.card_le_card hs
    _ ≤ (Finset.range T).card + (exceptionFinset F X).card := Finset.card_union_le _ _
    _ = T + exceptionCount F X := by simp [exceptionCount]
