-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR10.height_growth_sharp_dyadic
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:54:40.492923+00:00
-- url     : https://prove2.me/submissions/0b4e88be-3c77-4169-9229-3a70c66ce7e6

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Erdos269_JumpConstraintMajorant
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_PaperR7ActualOrbit
import Definitions.Def_ErdosProblems_Erdos269_PaperR7SeriesIdentification
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Definitions.Def_ErdosProblems_Erdos269_RationalityCarryBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7RationalBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7WindowResults
import Definitions.Def_ErdosProblems_Erdos269_PaperR8RankMajorant
import Definitions.Def_ErdosProblems_Erdos269_ActualSharpTailMajorantR10
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
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
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace PaperR7
end PaperR7

namespace PaperR8
end PaperR8

/-!
# The jump-constrained bound for the literal tail

The extra growth is proved directly for the three floor logarithms. This avoids
assuming an enumeration of the jump word or an unproved majorisation supplier.
At a dyadic starting point, d₂ ≤ 2d₃+1. Consequently the first k rank increases
multiply the height by at least 2^(k-j)3^j, j=(k+1)/3. The residue-three sum
then gives precisely the printed Q̃, with the existing actual rank-fibre bound.


-/

namespace ErdosProblems.Erdos269.PaperR10
open scoped BigOperators
open PaperR7 PaperR8







theorem dyadic_two_increment_le (a x : ℕ) (hx : 2 ^ a ≤ x) :
    Nat.log 2 x - a ≤ 2 * (Nat.log 3 x - Nat.log 3 (2 ^ a)) + 1 := by
  let b := Nat.log 3 (2 ^ a)
  let B := Nat.log 3 x
  let d := B - b
  have hb : b ≤ B := Nat.log_mono_right hx
  have hx0 : x ≠ 0 := (lt_of_lt_of_le (by positivity : 0 < 2 ^ a) hx).ne'
  have hlow : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 hx0
  have hbase : 3 ^ b ≤ 2 ^ a := Nat.pow_log_le_self 3 (by positivity)
  have hupper : x < 3 ^ (B + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < (3 : ℕ)) x
  have hsplit : B + 1 = b + (d + 1) := by dsimp [d]; omega
  have hcomp : x < 2 ^ (a + 2 * (d + 1)) := by
    calc
      x < 3 ^ (B + 1) := hupper
      _ = 3 ^ b * 3 ^ (d + 1) := by rw [hsplit, pow_add]
      _ ≤ 2 ^ a * 4 ^ (d + 1) := Nat.mul_le_mul hbase
        (Nat.pow_le_pow_left (by decide : 3 ≤ 4) _)
      _ = 2 ^ (a + 2 * (d + 1)) := by
        rw [pow_add (2 : ℕ) a (2 * (d + 1)), pow_mul]
        norm_num
  have hexp : Nat.log 2 x < a + 2 * (d + 1) := by
    by_contra h
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.le_of_not_gt h)
    exact (not_lt_of_ge (hp.trans hlow)) hcomp
  change Nat.log 2 x - a ≤ 2 * d + 1
  omega
end ErdosProblems.Erdos269.PaperR10

open scoped BigOperators
open PaperR7 PaperR8
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR10 in
open ErdosProblems.Erdos269.PaperR7 in
open ErdosProblems.Erdos269.PaperR8 in
theorem solution (a x : ℕ) (hx : 2 ^ a ≤ x) :
    threePrimeHeight 2 3 5 (2 ^ a) *
      sharpJumpDenom (heightRank235 x - paperJumpIndex a) ≤
        threePrimeHeight 2 3 5 x := by
  let b := Nat.log 3 (2 ^ a)
  let c := Nat.log 5 (2 ^ a)
  let A := Nat.log 2 x
  let B := Nat.log 3 x
  let C := Nat.log 5 x
  let d₂ := A - a
  let d₃ := B - b
  let d₅ := C - c
  let t := d₃ + d₅
  let k := heightRank235 x - paperJumpIndex a
  let j := (k + 1) / 3
  have ha : a ≤ A := by
    have h := Nat.log_mono_right (b := 2) hx
    simpa only [Nat.log_pow (by decide : 1 < (2 : ℕ))] using h
  have hb : b ≤ B := Nat.log_mono_right hx
  have hc : c ≤ C := Nat.log_mono_right hx
  have hk : k = d₂ + t := by
    dsimp [k, heightRank235, paperJumpIndex, d₂, d₃, d₅, t, A, B, C, b, c]
    dsimp [A, B, C, b, c] at ha hb hc
    omega
  have htwo : d₂ ≤ 2 * d₃ + 1 := dyadic_two_increment_le a x hx
  have hj : j ≤ t := by dsimp [j]; omega
  have he : k - j = d₂ + (t - j) := by omega
  have hlocal : sharpJumpDenom k ≤ 2 ^ d₂ * 3 ^ d₃ * 5 ^ d₅ := by
    calc
      sharpJumpDenom k = 2 ^ d₂ * (2 ^ (t - j) * 3 ^ j) := by
        change 2 ^ (k - j) * 3 ^ j = _
        rw [he, pow_add]
        ring
      _ ≤ 2 ^ d₂ * (3 ^ (t - j) * 3 ^ j) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
          (Nat.pow_le_pow_left (by decide : 2 ≤ 3) _))
      _ = 2 ^ d₂ * 3 ^ d₃ * 3 ^ d₅ := by
        rw [← pow_add, Nat.sub_add_cancel hj]
        dsimp [t]
        rw [pow_add]
        ring
      _ ≤ 2 ^ d₂ * 3 ^ d₃ * 5 ^ d₅ := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by decide : 3 ≤ 5) _)
  have htel : threePrimeHeight 2 3 5 (2 ^ a) *
      (2 ^ d₂ * 3 ^ d₃ * 5 ^ d₅) = threePrimeHeight 2 3 5 x := by
    have hea : a + d₂ = A := by dsimp [d₂]; omega
    have heb : b + d₃ = B := by dsimp [d₃]; omega
    have hec : c + d₅ = C := by dsimp [d₅]; omega
    change (2 ^ Nat.log 2 (2 ^ a) * 3 ^ b * 5 ^ c) *
      (2 ^ d₂ * 3 ^ d₃ * 5 ^ d₅) = 2 ^ A * 3 ^ B * 5 ^ C
    rw [Nat.log_pow (by decide : 1 < (2 : ℕ))]
    calc
      _ = (2 ^ a * 2 ^ d₂) * (3 ^ b * 3 ^ d₃) * (5 ^ c * 5 ^ d₅) := by ring
      _ = _ := by rw [← pow_add, ← pow_add, ← pow_add, hea, heb, hec]
  exact (Nat.mul_le_mul_left (threePrimeHeight 2 3 5 (2 ^ a)) hlocal).trans_eq htel
