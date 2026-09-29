-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.progressionMean_kernel_le_gcdMean_add_error
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:10:15.783187+00:00
-- url     : https://prove2.me/submissions/fad3f584-e4ff-4db3-93ca-7ac65f8c7027

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
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_kernel_den_pos
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_sum_kernelWeight_le_gcdBlockCount
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
    (L d T : ℕ) (hL : 0 < L) (hd : 0 < d) (hT : 0 < T) :
    progressionMean L T (kernelWeight B d) ≤
      (Nat.gcd L d : ℝ) / ((d : ℝ) * (B ^ Nat.gcd L d - 1)) +
      1 / ((T : ℝ) * (B ^ Nat.gcd L d - 1)) := by
  let g := Nat.gcd L d
  let h := d / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hL
  have hh : 0 < h := Nat.div_pos (Nat.gcd_le_right L hd) hg
  have hdFac : g * h = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right L d)
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hden : 0 < B ^ g - 1 := kernel_den_pos hB hg
  have hratio : (T : ℝ) / h = (T : ℝ) * g / d := by
    rw [← hdFac]
    push_cast
    have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    field_simp [hgR, hhR.ne']
  have hquot : ((T / h : ℕ) : ℝ) ≤ (T : ℝ) * g / d := by
    rw [← hratio]
    -- Mathlib/Data/Nat/Cast/Order/Field.lean: Nat.cast_div_le.
    exact Nat.cast_div_le
  have hsum := sum_kernelWeight_le_gcdBlockCount B hB L d T hL hd
  unfold progressionMean
  calc
    _ ≤ ((((T / h : ℕ) : ℝ) + 1) / (B ^ g - 1)) / T :=
      div_le_div_of_nonneg_right hsum hTR.le
    _ ≤ (((T : ℝ) * g / d + 1) / (B ^ g - 1)) / T := by
      have hquot' : ((T / h : ℕ) : ℝ) + 1 ≤ (T : ℝ) * g / d + 1 := by
        linarith only [hquot]
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hquot' hden.le) hTR.le
    _ = _ := by
      change ((T : ℝ) * g / d + 1) / (B ^ g - 1) / T =
        (g : ℝ) / ((d : ℝ) * (B ^ g - 1)) + 1 / ((T : ℝ) * (B ^ g - 1))
      field_simp [hTR.ne', hdR.ne', hden.ne']
      <;> ring
end
