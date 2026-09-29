-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR10.running_lcm_real_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:25:39.042519+00:00
-- url     : https://prove2.me/submissions/9f5687f5-c8e6-4920-895f-6e10cf42b03b

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_RealCutoffR10
import Theorems.Thm_ErdosProblems_Erdos269_smoothPrefixLcm_eq_threePrimeHeight
import Theorems.Thm_ErdosProblems_Erdos269_PaperR10_realPrefixExponents_eq
import Theorems.Thm_ErdosProblems_Erdos269_PaperR10_realThreePrimeHeight_eq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

                                                                               
                                                                                
                                                                         
                                        

namespace ErdosProblems.Erdos269.PaperR10
open scoped BigOperators
end ErdosProblems.Erdos269.PaperR10

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR10 in
theorem solution {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x : ℝ} (hx : 1 ≤ x) :
    realPrefixLcm p q r x = realThreePrimeHeight p q r x := by
  have hn : ⌊x⌋₊ ≠ 0 := by have h := (Nat.one_le_floor_iff x).mpr hx; omega
  rw [realThreePrimeHeight_eq hp.one_lt hq.one_lt hr.one_lt hx]
  unfold realPrefixLcm
  rw [realPrefixExponents_eq hp.one_lt hq.one_lt hr.one_lt hx]
  exact smoothPrefixLcm_eq_threePrimeHeight hp hq hr hpq hpr hqr hn
