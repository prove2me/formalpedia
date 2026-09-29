-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.literal_integer_forcing_and_four_radices
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:21:14.084796+00:00
-- url     : https://prove2.me/submissions/96617f40-6b4c-42b5-bb6c-0eb4939adb5b

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_literalForcing235_eq_digit
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_orderedDigit235_pos
import Theorems.Thm_ErdosProblems_Erdos269_dyadicBlockBase235_cases
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

/-!
# Round 7: literal forcing, infinite digit expansion and scaled dichotomy

Targets: short-note `res:dyadic-alphabet`, the dynamical clauses of
`res:actual-orbit`, and long-record `res:actual-orbit`.
The total smooth-series reindexing is supplied separately in
`PaperR7SeriesIdentification`; nothing here silently identifies a formal tsum
with the smooth-number series without that bridge.

No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7
open scoped BigOperators
end ErdosProblems.Erdos269.PaperR7

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution (a : ℕ) :
    (∃ m : ℕ, 0 < m ∧ literalForcing235 a = (m : ℚ)) ∧
    (dyadicBlockBase235 a = 2 ∨ dyadicBlockBase235 a = 6 ∨
      dyadicBlockBase235 a = 10 ∨ dyadicBlockBase235 a = 30) :=
  ⟨⟨dyadicOrderedBlockDigit235 a, orderedDigit235_pos a,
      literalForcing235_eq_digit a⟩, dyadicBlockBase235_cases a⟩
