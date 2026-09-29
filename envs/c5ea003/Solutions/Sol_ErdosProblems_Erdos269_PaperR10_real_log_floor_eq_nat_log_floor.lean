-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR10.real_log_floor_eq_nat_log_floor
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:17:55.19089+00:00
-- url     : https://prove2.me/submissions/34c5b1f5-ee35-40f9-9675-fa1f7b2d7b95

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

/-- A real cutoff and its natural floor select exactly the same integer powers. -/
theorem power_brackets_real_cutoff {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x) :
    ((p ^ Nat.log p ⌊x⌋₊ : ℕ) : ℝ) ≤ x ∧
      x < ((p ^ (Nat.log p ⌊x⌋₊ + 1) : ℕ) : ℝ) := by
  have hn : ⌊x⌋₊ ≠ 0 := by
    have h := (Nat.one_le_floor_iff x).mpr hx
    omega
  constructor
  · have hpow : ((p ^ Nat.log p ⌊x⌋₊ : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self p hn
    exact hpow.trans (Nat.floor_le (le_trans (by norm_num : (0 : ℝ) ≤ 1) hx))
  · exact Nat.lt_of_floor_lt
      (Nat.lt_pow_succ_log_self hp ⌊x⌋₊)
end ErdosProblems.Erdos269.PaperR10

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR10 in
theorem solution {p : ℕ} (hp : 1 < p)
    {x : ℝ} (hx : 1 ≤ x) :
    ⌊Real.logb p x⌋₊ = Nat.log p ⌊x⌋₊ := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hn : 0 ≤ Real.logb p x := (Real.logb_nonneg_iff hpR hx0).mpr hx
  have h := power_brackets_real_cutoff hp hx
  apply (Nat.floor_eq_iff hn).mpr
  constructor
  · apply (Real.le_logb_iff_rpow_le hpR hx0).mpr
    simpa only [Real.rpow_natCast, Nat.cast_pow] using h.1
  · have hh : Real.logb p x < ((Nat.log p ⌊x⌋₊ + 1 : ℕ) : ℝ) := by
      apply (Real.logb_lt_iff_lt_rpow hpR hx0).mpr
      simpa only [Real.rpow_natCast, Nat.cast_pow] using h.2
    simpa only [Nat.cast_add, Nat.cast_one] using hh
