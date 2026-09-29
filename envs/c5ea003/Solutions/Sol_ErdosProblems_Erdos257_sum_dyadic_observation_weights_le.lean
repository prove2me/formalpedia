-- Prove2me | solution 1 for ErdosProblems.Erdos257.sum_dyadic_observation_weights_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:05:47.931482+00:00
-- url     : https://prove2.me/submissions/8a4af7bb-52be-4024-928a-24e3d2f931b9

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
import Theorems.Thm_ErdosProblems_Erdos257_sum_half_pow_le_twice_min
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
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

namespace ErdosProblems.Erdos257
end ErdosProblems.Erdos257

namespace TotientTailPeriodKiller
end TotientTailPeriodKiller

/-!
# Finite averaging for divisibility-weighted supports

The weighted support proof needs two finite estimates before taking any
limit. The orbit estimate retains the geometric GCD factor discarded by the
reciprocal-mass bound. The observation-length estimate sums incomplete-period
errors across dyadic scales, charging each conductor only once.

These are the actual finite estimates used in the analytic proof. The
prime-part decomposition and the final choice of scales are separate steps.
-/

namespace ErdosProblems.Erdos257
open Erdos257PeriodNoncollapse TotientTailPeriodKiller

noncomputable section
end
end ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse TotientTailPeriodKiller
open ErdosProblems in
open ErdosProblems.Erdos257 in
theorem solution (J : Finset ℕ) (Q a : ℕ)
    (ha : 0 < a) :
    ∑ j ∈ J.filter (fun j => a ≤ Q * 2 ^ j), (1 / 2 : ℝ) ^ j ≤
      2 * (Q : ℝ) / a := by
  classical
  let s := J.filter (fun j => a ≤ Q * 2 ^ j)
  by_cases hs : s.Nonempty
  · let m := s.min' hs
    have hm : m ∈ s := Finset.min'_mem _ hs
    have ham : a ≤ Q * 2 ^ m := (Finset.mem_filter.mp hm).2
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hamR : (a : ℝ) ≤ (Q : ℝ) * (2 : ℝ) ^ m := by exact_mod_cast ham
    have hmul : (1 / 2 : ℝ) ^ m * (2 : ℝ) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    have hscale := mul_le_mul_of_nonneg_left hamR
      (show 0 ≤ (1 / 2 : ℝ) ^ m by positivity)
    have hproduct : (1 / 2 : ℝ) ^ m * ((Q : ℝ) * (2 : ℝ) ^ m) = Q := by
      calc
        _ = (Q : ℝ) * ((1 / 2 : ℝ) ^ m * (2 : ℝ) ^ m) := by ring
        _ = Q := by rw [hmul]; ring
    rw [hproduct] at hscale
    have hbound : 2 * (1 / 2 : ℝ) ^ m ≤ 2 * (Q : ℝ) / a := by
      rw [le_div_iff₀ haR]
      nlinarith
    exact (sum_half_pow_le_twice_min s m
      (fun j hj => Finset.min'_le s j hj)).trans hbound
  · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change (∑ j ∈ s, (1 / 2 : ℝ) ^ j) ≤ _
    rw [this]
    simp only [Finset.sum_empty]
    positivity
