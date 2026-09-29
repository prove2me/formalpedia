-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.sum_kernelWeight_le_gcdBlockCount
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:08:54.711296+00:00
-- url     : https://prove2.me/submissions/92550b30-5ef9-4217-a4ae-52ba673350b1

import Definitions.Def_Erdos249257_TotientTailPeriodKiller
import Definitions.Def_Erdos249257_CarrySurvivorExtinction
import Definitions.Def_Erdos249257_LcmConeFlatness
import Definitions.Def_Erdos249257_LcmConeNonflat
import Definitions.Def_Erdos249257_SternBrocotRunGeometry
import Definitions.Def_Erdos249257_CertificateKernel
import Definitions.Def_Erdos249257_GenericTailOrbitRigidity
import Definitions.Def_Erdos249257_GreedyAchievementSet
import Definitions.Def_Erdos249257_RationalSupportCarrySkeleton
import Definitions.Def_Erdos249257_ReciprocalSupportIrrationality
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
import Theorems.Thm_Erdos249257_blockRemainder_le_blockSum
import Theorems.Thm_Erdos249257_sum_range_eq_mul_blockSum_add_blockRemainder
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_kernelWeight_nonneg
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_sum_kernelWeight_gcdOrbit_block
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Set
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Perfect

namespace Erdos257PeriodNoncollapse
end Erdos257PeriodNoncollapse

namespace Erdos257PeriodNoncollapse.TotientTailPeriodKiller
end Erdos257PeriodNoncollapse.TotientTailPeriodKiller

/-!
# Real-base complete-orbit bookkeeping

Generalises the *repaired existing* binary proof in
Erdos257PeriodNoncollapse/ReciprocalSupportIrrationality.lean, lines 153--280,
without changing its finite permutation argument. Unlike the binary result,
this applies at B=2^α for α arbitrarily close to zero.
NOT COMPILED in this return. No premise is an irrationality conclusion.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.TotientTailPeriodKiller
open ErdosProblems.Erdos257.PaperCompleteR7
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.TotientTailPeriodKiller
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (B : ℝ) (hB : 1 < B)
    (L d T : ℕ) (hL : 0 < L) (hd : 0 < d) :
    (∑ m ∈ Finset.range T, kernelWeight B d ((m + 1) * L)) ≤
      (((T / (d / Nat.gcd L d) : ℕ) : ℝ) + 1) / (B ^ Nat.gcd L d - 1) := by
  let g := Nat.gcd L d
  let h := d / g
  let C : ℝ := 1 / (B ^ g - 1)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hL
  have hh : 0 < h := Nat.div_pos (Nat.gcd_le_right L hd) hg
  have hblock : ∀ q : ℕ,
      (∑ j ∈ Finset.range h, kernelWeight B d ((q * h + j + 1) * L)) = C := by
    intro q
    exact sum_kernelWeight_gcdOrbit_block B hB L d hL hd q
  have hr := Erdos249257.blockRemainder_le_blockSum
    (fun k => kernelWeight B d ((k + 1) * L)) h C hh
    (fun k => kernelWeight_nonneg hB d _) hblock T
  rw [Erdos249257.sum_range_eq_mul_blockSum_add_blockRemainder _ h C hblock T]
  calc
    _ ≤ ((T / h : ℕ) : ℝ) * C + C := add_le_add le_rfl hr
    _ = _ := by dsimp [C, h, g]; ring
end
