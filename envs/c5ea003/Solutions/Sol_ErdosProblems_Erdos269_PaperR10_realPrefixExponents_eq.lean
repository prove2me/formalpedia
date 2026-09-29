-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR10.realPrefixExponents_eq
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:21:03.516162+00:00
-- url     : https://prove2.me/submissions/adcd90c7-60d3-4ee5-9416-73c8b87b2c22

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
import Theorems.Thm_ErdosProblems_Erdos269_PaperR10_real_log_floor_eq_nat_log_floor
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
theorem solution {p q r : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hr : 1 < r) {x : ℝ} (hx : 1 ≤ x) :
    realPrefixExponents p q r x = smoothPrefixExponents p q r ⌊x⌋₊ := by
  classical
  unfold realPrefixExponents smoothPrefixExponents
  rw [real_log_floor_eq_nat_log_floor hp hx,
    real_log_floor_eq_nat_log_floor hq hx, real_log_floor_eq_nat_log_floor hr hx]
  ext e
  simp only [Finset.mem_filter, Nat.le_floor_iff (le_trans (by norm_num : (0 : ℝ) ≤ 1) hx)]
