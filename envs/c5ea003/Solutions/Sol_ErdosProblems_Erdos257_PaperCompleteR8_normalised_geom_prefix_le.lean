-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.normalised_geom_prefix_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:33:43.1173+00:00
-- url     : https://prove2.me/submissions/91fac499-6e8f-4db5-a0ad-fc679e2786cb

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

namespace Erdos257PeriodNoncollapse
end Erdos257PeriodNoncollapse

namespace ErdosProblems.Erdos257.DyadicShellSynchronisation
end ErdosProblems.Erdos257.DyadicShellSynchronisation

/-!
# The finite estimate (S)

All three regimes refer to the actual modular atom, not abstract error terms.
The complete-orbit argument is in OrbitBound. The dyadic reciprocal-tail bound
is reused from the compiled WeightedSupportAveraging module. This file proves
no-wrap and transition bounds and then assembles the uniform finite estimate.
NOT COMPILED in this return.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems.Erdos257.DyadicShellSynchronisation
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems.Erdos257.DyadicShellSynchronisation
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution {B : ℝ} (hB : 1 ≤ B)
    (n d : ℕ) (hnd : n ≤ d) :
    (d : ℝ) * (∑ i ∈ Finset.range n, B ^ i) ≤
      (n : ℝ) * (∑ i ∈ Finset.range d, B ^ i) := by
  have hBn : 0 ≤ B ^ n := pow_nonneg (le_trans zero_le_one hB) n
  have hhead : (∑ i ∈ Finset.range n, B ^ i) ≤ (n : ℝ) * B ^ n := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, B ^ n := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_right₀ hB (Finset.mem_range.mp hi).le
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have htail : ((d - n : ℕ) : ℝ) * B ^ n ≤
      ∑ i ∈ Finset.range (d - n), B ^ (n + i) := by
    calc
      _ = ∑ _i ∈ Finset.range (d - n), B ^ n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _hi
        exact pow_le_pow_right₀ hB (Nat.le_add_right n i)
  have hsplit : (∑ i ∈ Finset.range d, B ^ i) =
      (∑ i ∈ Finset.range n, B ^ i) +
        ∑ i ∈ Finset.range (d - n), B ^ (n + i) := by
    -- Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean: sum_range_add.
    have hndeq : n + (d - n) = d := by omega
    simpa only [hndeq] using
      (Finset.sum_range_add (fun i => B ^ i) n (d - n))
  have hsub : ((d - n : ℕ) : ℝ) = (d : ℝ) - (n : ℝ) := Nat.cast_sub hnd
  have hhead' := mul_le_mul_of_nonneg_left hhead (Nat.cast_nonneg (d - n))
  have htail' := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg n)
  rw [hsub] at hhead' htail'
  rw [hsplit]
  nlinarith only [hhead', htail']
end
