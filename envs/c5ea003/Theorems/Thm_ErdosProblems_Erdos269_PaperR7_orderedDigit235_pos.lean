-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperR7_orderedDigit235_pos
-- name    : ErdosProblems.Erdos269.PaperR7.orderedDigit235_pos
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:15:57.423674+00:00
-- url     : https://prove2.me/theorems/fb57e28b-6838-4981-8ce2-0728a509abfb
-- title:
--   OrderedDigit235 pos
-- statement:
--   Every ordered dyadic block digit is strictly positive.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperR7ActualOrbit.lean#L38-L45
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

theorem ErdosProblems.Erdos269.PaperR7.orderedDigit235_pos (a : ℕ) : 0 < dyadicOrderedBlockDigit235 a := by sorry
