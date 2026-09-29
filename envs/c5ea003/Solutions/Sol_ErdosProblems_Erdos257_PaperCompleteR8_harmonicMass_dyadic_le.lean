-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.harmonicMass_dyadic_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:19:15.294412+00:00
-- url     : https://prove2.me/submissions/bd06c802-aec7-47f7-8726-e2bd62164f7f

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
import Definitions.Def_Erdos249257_AllBaseReciprocalSupportIrrationality
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_Displacement
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_AnalyticTargets
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedPrimeProfile
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedFiniteEstimates
import Mathlib
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

/-!
# Finite weighted estimates with an explicit observation window

The high-GCD remainder is charged against a dyadic harmonic
bound, not against the cardinality of an unbounded conductor support.
The future-conductor contribution is bounded geometrically before any
infinite interchange. All constants here are deliberately non-sharp.
-/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7









theorem harmonicMass_le_self (n : ℕ) : harmonicMass n ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hpos : (0 : ℝ) < ((i+1:ℕ):ℝ) := by positivity
      apply (div_le_one hpos).mpr
      exact_mod_cast (Nat.succ_pos i)
    _ = _ := by simp

theorem harmonicMass_double_le (n : ℕ) : harmonicMass (2*n) ≤ harmonicMass n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [harmonicMass]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : (∑ i ∈ Finset.range n, 1 / ((n+i+1:ℕ):ℝ)) ≤ 1 := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, 1/(n:ℝ) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact one_div_le_one_div_of_le hnR (by exact_mod_cast (by omega : n ≤ n+i+1))
      _ = 1 := by simp [hnR.ne']
  have heq : harmonicMass (2*n) = harmonicMass n +
      ∑ i ∈ Finset.range n, 1 / ((n+i+1:ℕ):ℝ) := by
    rw [show 2*n=n+n by omega, harmonicMass, Finset.sum_range_add]
    rfl
  rw [heq]
  exact add_le_add (le_refl _) ht
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (Q j : ℕ) : harmonicMass (Q*2^j) ≤ (Q:ℝ) + j := by
  induction j with
  | zero => simpa using harmonicMass_le_self Q
  | succ j ih =>
    have heq : Q*2^(j+1)=2*(Q*2^j) := by rw [pow_succ]; ring
    rw [heq]
    have hh := harmonicMass_double_le (Q*2^j)
    push_cast
    linarith only [hh, ih]
end
