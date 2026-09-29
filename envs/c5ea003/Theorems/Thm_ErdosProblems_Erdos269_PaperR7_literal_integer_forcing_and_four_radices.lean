-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperR7_literal_integer_forcing_and_four_radices
-- name    : ErdosProblems.Erdos269.PaperR7.literal_integer_forcing_and_four_radices
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:16:37.42428+00:00
-- url     : https://prove2.me/theorems/78add230-b863-43d6-8668-8eba9e7dfd6a
-- title:
--   Literal integer forcing and four radices
-- statement:
--   At each scale the literal forcing is a positive integer, and the block base belongs to {2,6,10,30}.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperR7ActualOrbit.lean#L47-L53
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

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


open scoped BigOperators

open ErdosProblems.Erdos269.PaperR7

theorem ErdosProblems.Erdos269.PaperR7.literal_integer_forcing_and_four_radices (a : ℕ) :
    (∃ m : ℕ, 0 < m ∧ literalForcing235 a = (m : ℚ)) ∧
    (dyadicBlockBase235 a = 2 ∨ dyadicBlockBase235 a = 6 ∨
      dyadicBlockBase235 a = 10 ∨ dyadicBlockBase235 a = 30) := by sorry
