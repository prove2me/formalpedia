-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.dyadic_alphabet_whole
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:02:17.393113+00:00
-- url     : https://prove2.me/submissions/138b3479-78de-44ea-b596-655ae5dbd8aa

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Erdos269_PaperR7ActualOrbit
import Definitions.Def_ErdosProblems_Erdos269_PaperR9SourceCounts
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_literalForcing235_eq_digit
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_literal_integer_forcing_and_four_radices
import Theorems.Thm_ErdosProblems_Erdos269_PaperR9_orderedDigitExact_correct
import Theorems.Thm_ErdosProblems_Erdos269_dyadicBlockBase235_four
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ErdosProblems.Erdos269.PaperCompleteR20
end ErdosProblems.Erdos269.PaperCompleteR20

namespace PaperR7
end PaperR7

namespace PaperR9
end PaperR9

/-! The full dyadic alphabet statement includes its non-positional warning.
The printed scale-four example is checked by the Lean kernel after transport
through the proved exact digit evaluator. -/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open PaperR7 PaperR9

theorem actual_digit_four : dyadicOrderedBlockDigit235 4 = 65 := by
  rw [← orderedDigitExact_correct 4]
  decide +kernel

theorem actual_base_four : dyadicBlockBase235 4 = 30 := by
  exact dyadicBlockBase235_four
end ErdosProblems.Erdos269.PaperCompleteR20

open PaperR7 PaperR9
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR9 in
theorem solution :
    (∀ a : ℕ,
      (∃ m : ℕ, 0 < m ∧ literalForcing235 a = (m : ℚ)) ∧
      (dyadicBlockBase235 a = 2 ∨ dyadicBlockBase235 a = 6 ∨
        dyadicBlockBase235 a = 10 ∨ dyadicBlockBase235 a = 30)) ∧
    literalForcing235 4 = 65 ∧ dyadicBlockBase235 4 = 30 ∧
    (∃ a : ℕ, dyadicBlockBase235 a < dyadicOrderedBlockDigit235 a) := by
  refine ⟨literal_integer_forcing_and_four_radices, ?_, actual_base_four, 4, ?_⟩
  · rw [literalForcing235_eq_digit, actual_digit_four]
    norm_num
  · rw [actual_base_four, actual_digit_four]
    norm_num
